import Blotto.RationalAllocationProgram
import Blotto.CachedWordControllerRefinement
import Blotto.WordMappedIndexedRefinement
import Blotto.RationalResourceArray

/-! An array-valued terminal controller performs whole-row emission before
returning its successful payload. Projection preserves the complete indexed
result, including failure and the consumed-bit position. -/

namespace Blotto

theorem WordStateMachine.mapped_compose {S α β γ : Type*}
    (m : WordStateMachine S α) (f : α → β) (g : β → γ) :
    (m.mapped f).mapped g = m.mapped (fun x => g (f x)) := by
  cases m with
  | mk step rank progress =>
    unfold WordStateMachine.mapped
    congr 1
    funext s
    change ((step s).mapValue f).mapValue g = (step s).mapValue (fun x => g (f x))
    cases step s <;> rfl

structure RationalStoredAllocationProgram (n C : ℕ) where
  State : Type
  machine : WordStateMachine State (RationalResourceArray n)
  start : State
  rank_le : machine.rank start ≤ C

namespace RationalStoredAllocationProgram

def ofProgram {n m C : ℕ} (p : RationalAllocationProgram m C)
    (emit : (Fin m → ℚ) → RationalResourceArray n) : RationalStoredAllocationProgram n C :=
  ⟨p.State, p.machine.mapped emit, p.start, p.rank_le⟩

def reference {n C : ℕ} (p : RationalStoredAllocationProgram n C) : RationalAllocationProgram n C :=
  ⟨p.State, p.machine.mapped RationalResourceArray.allocation, p.start, p.rank_le⟩

def widen {n C D : ℕ} (p : RationalStoredAllocationProgram n C) (h : C ≤ D) :
    RationalStoredAllocationProgram n D := ⟨p.State, p.machine, p.start, p.rank_le.trans h⟩

theorem reference_from {n m C : ℕ} (p : RationalAllocationProgram m C)
    (emit : (Fin m → ℚ) → RationalResourceArray n) :
    (ofProgram p emit).reference = p.mapped (fun y => (emit y).allocation) := by
  unfold ofProgram reference RationalAllocationProgram.mapped
  dsimp only
  congr 1
  exact WordStateMachine.mapped_compose p.machine emit RationalResourceArray.allocation

theorem reference_widen {n C D : ℕ} (p : RationalStoredAllocationProgram n C) (h : C ≤ D) :
    (p.widen h).reference = p.reference.widen h := rfl

theorem cached_projection {n C : ℕ} (p : RationalStoredAllocationProgram n C)
    (N : ℕ) (bits : Fin N → Bool) (cursor : CachedWordCursor p.State) (pos : ℕ) (hp : pos ≤ N) :
    WordMappedIndexedRefinement.mapResult RationalResourceArray.allocation
      (p.machine.runCachedIndexed N bits cursor pos hp) =
      p.reference.machine.runCachedIndexed N bits cursor pos hp := by
  change WordMappedIndexedRefinement.mapResult RationalResourceArray.allocation
    (p.machine.runCachedIndexed N bits cursor pos hp) =
    (p.machine.mapped RationalResourceArray.allocation).runCachedIndexed N bits cursor pos hp
  rw [WordStateMachine.runCachedIndexed_refines, WordStateMachine.runCachedIndexed_refines]
  exact (WordMappedIndexedRefinement.indexed_refines p.machine _ N bits cursor.reference pos hp).symm

end RationalStoredAllocationProgram
end Blotto
