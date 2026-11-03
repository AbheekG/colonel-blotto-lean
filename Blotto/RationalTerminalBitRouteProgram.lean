import Blotto.RationalBitRouteEmission
import Blotto.RationalTerminalProgram

/-! The terminal sampler can use the decoded binary route region for its
whole-row output map. Its complete program equals the retained sampler, so
controller outputs and every fallback retain their original budget guarantee.
Emission decoding/time and full source integration are separate. -/

namespace Blotto.RationalTerminalLotto

def programWithBitRoutes {n : ℕ} {β : Type*} (i : RationalTerminalLotto n) (W : ℕ)
    (hFit : ∀ e ∈ (RationalTerminalPacking.prepare i).routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : TableStoreState (n * W) Bool β) (K : ℕ) (outerBits scalarBits : Fin K → Bool) : RationalAllocationProgram n 80 :=
  let packed := RationalTerminalPacking.prepare i
  let memory := (packed.runRouteBitStore W hFit state).cells
  match h : i.pivot with
  | none =>
    (((packed.uniformSpec (i.pivot_none h)).program i.groups_count K scalarBits).mapped
      (fun y => (packed.emitFromBits memory y).allocation)).widen (by decide)
  | some pivot =>
    ((packed.mixedSpec pivot (i.pivot_some h)).program i.groups_count K outerBits scalarBits).mapped
      (fun y => (packed.emitMixedFromBits memory pivot y).allocation)

theorem programWithBitRoutes_eq {n : ℕ} {β : Type*} (i : RationalTerminalLotto n) (W : ℕ)
    (hFit : ∀ e ∈ (RationalTerminalPacking.prepare i).routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : TableStoreState (n * W) Bool β) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    i.programWithBitRoutes W hFit state K outerBits scalarBits = i.program K outerBits scalarBits := by
  let packed := RationalTerminalPacking.prepare i
  have hEmit : (fun y => (packed.emitFromBits (packed.runRouteBitStore W hFit state).cells y).allocation) =
      (fun y => (packed.prepareOutput.emit y).allocation) := by
    funext y
    exact packed.emitFromBits_after_store W hFit state y
  have hMixed : ∀ pivot, (fun y => (packed.emitMixedFromBits (packed.runRouteBitStore W hFit state).cells pivot y).allocation) =
      (fun y => (packed.prepareOutput.emitMixed pivot y).allocation) := by
    intro pivot
    funext y
    exact packed.emitMixedFromBits_after_store W hFit state pivot y
  dsimp only [packed] at hEmit hMixed
  unfold programWithBitRoutes program
  dsimp only
  split
  · rename_i hNone
    simp only [hEmit]
    split
    · rfl
    · rename_i pivot hSome
      rw [hNone] at hSome
      cases hSome
  · rename_i pivot hSome
    simp only [hMixed]
    split
    · rename_i hNone
      rw [hSome] at hNone
      cases hNone
    · rename_i other hOther
      have hEq : pivot = other := Option.some.inj (hSome.symm.trans hOther)
      subst other
      rfl

theorem programWithBitRoutes_leavesBudget {n : ℕ} {β : Type*} (i : RationalTerminalLotto n) (W : ℕ)
    (hFit : ∀ e ∈ (RationalTerminalPacking.prepare i).routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : TableStoreState (n * W) Bool β) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    (i.programWithBitRoutes W hFit state K outerBits scalarBits).LeavesBudget i.B := by
  rw [i.programWithBitRoutes_eq]
  exact i.program_leavesBudget K outerBits scalarBits

theorem programWithBitRoutes_sample_fullBudget {n : ℕ} {β : Type*} (i : RationalTerminalLotto n) (W : ℕ)
    (hFit : ∀ e ∈ (RationalTerminalPacking.prepare i).routeStoreProgram, (BinaryRouteFrame.encode e.2).length ≤ W)
    (state : TableStoreState (n * W) Bool β) (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    FullBudget (i.B : ℝ) (fun j => ((i.programWithBitRoutes W hFit state K outerBits scalarBits).sample R choiceBits j : ℝ)) := by
  rw [i.programWithBitRoutes_eq]
  exact i.program_sample_fullBudget K R outerBits scalarBits choiceBits

end Blotto.RationalTerminalLotto
