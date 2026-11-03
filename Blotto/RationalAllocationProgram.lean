import Blotto.RationalMachineLaw
import Blotto.WordMachineFallback
import Blotto.WordMachineChoice

/-! A packaged native rational controller retains its state type, initial
state and rank certificate. It constructs no specification tree at runtime. -/

namespace Blotto

structure RationalAllocationProgram (n C : ℕ) where
  State : Type
  machine : WordStateMachine State (Fin n → ℚ)
  start : State
  rank_le : machine.rank start ≤ C

namespace RationalAllocationProgram

def mapped {n m C : ℕ} (p : RationalAllocationProgram n C) (f : (Fin n → ℚ) → (Fin m → ℚ)) :
    RationalAllocationProgram m C := ⟨p.State, p.machine.mapped f, p.start, p.rank_le⟩

def widen {n C D : ℕ} (p : RationalAllocationProgram n C) (h : C ≤ D) : RationalAllocationProgram n D :=
  ⟨p.State, p.machine, p.start, p.rank_le.trans h⟩

def LeavesBudget {n C : ℕ} (p : RationalAllocationProgram n C) (B : ℚ) : Prop :=
  (p.machine.specification p.start).decode.ForLeaves (fun x => FullBudget (B : ℝ) (fun j => (x j : ℝ)))

def fallback {n C : ℕ} (p : RationalAllocationProgram n C) : Fin n → ℚ := p.machine.chooseLeaf p.start

def sample {n C : ℕ} (p : RationalAllocationProgram n C) (R : ℕ) (bits : Fin R → Bool) : Fin n → ℚ :=
  p.machine.output R p.start p.fallback bits

noncomputable def idealLaw {n C : ℕ} (p : RationalAllocationProgram n C) : Mixed n := p.machine.rationalIdealLaw p.start

noncomputable def sampleLaw {n C : ℕ} (p : RationalAllocationProgram n C) (R : ℕ) : Mixed n :=
  p.machine.rationalCappedLaw R p.start p.fallback

theorem fallback_fullBudget {n C : ℕ} (p : RationalAllocationProgram n C) {B : ℚ} (h : p.LeavesBudget B) :
    FullBudget (B : ℝ) (fun j => (p.fallback j : ℝ)) :=
  p.machine.chooseLeaf_forLeaves p.start _ h

theorem sample_fullBudget {n C : ℕ} (p : RationalAllocationProgram n C) {B : ℚ} (h : p.LeavesBudget B)
    (R : ℕ) (bits : Fin R → Bool) : FullBudget (B : ℝ) (fun j => (p.sample R bits j : ℝ)) := by
  rw [sample, WordStateMachine.output_refines]
  exact WordChoiceTree.output_forLeaves _ _ _ _ _ h (p.fallback_fullBudget h)

theorem sampleLaw_CDF_error {n C : ℕ} (p : RationalAllocationProgram n C) (K : ℕ) :
    CDFClose (p.sampleLaw (3 * (C + K))) p.idealLaw (1 / (2 : ℝ) ^ K) :=
  p.machine.rationalCappedLaw_CDF_error C K p.start p.rank_le p.fallback

theorem mapped_leavesBudget {n m C : ℕ} (p : RationalAllocationProgram n C) (f : (Fin n → ℚ) → (Fin m → ℚ))
    {B D : ℚ} (h : p.LeavesBudget B)
    (hf : ∀ x, FullBudget (B : ℝ) (fun j => (x j : ℝ)) → FullBudget (D : ℝ) (fun j => (f x j : ℝ))) :
    (p.mapped f).LeavesBudget D := by
  change ((p.machine.mapped f).specification p.start).decode.ForLeaves _
  rw [WordStateMachine.mapped_specification]
  apply WordChoiceTree.map_forLeaves
  exact WordChoiceTree.forLeaves_mono _ _ _ hf h

end RationalAllocationProgram
end Blotto
