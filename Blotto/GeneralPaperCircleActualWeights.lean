import Blotto.GeneralPaperCircleHardBudget

/-! Circle weights from the actual original-input reduction return.
Their sum and positivity are derived, never supplied as a lifting oracle.
These are erased observations of retained arrays; no replay or new sum pass
is added to execution. Restoring original field identities remains separate. -/
namespace Blotto.GeneralPaperCircleActualWeights
open GeneralPaperLightFieldScan GeneralPaperLightFieldIntegerBalance GeneralPaperLightFieldOrder
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

theorem light_balance {n : ℕ} (bits : Bool) (model : RationalCostModel) (W r Q : ℕ) (weights : FixedArrayTable n ℕ)
    (c : ℕ) (hc : c≤n) :
    weightSum weights (scan bits model W r Q weights c hc).1.light=(scan bits model W r Q weights c hc).1.lightWeight := by
  induction c with
  | zero => simp only [scan,empty]
  | succ c ih =>
    have h := ih (by omega)
    rw [state_step]
    split_ifs
    · simp only [push,h]
    · exact h

theorem classified_sum {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ) :
    let state := (GeneralPaperLightFieldClassification.run bits model W k Q weights).1.1
    (∑ i:Fin state.light.size,weights.read (index state.light i))=state.lightWeight := by
  rw [GeneralPaperLightFieldClassification.data]
  dsimp only
  rw [fin_sum]
  exact light_balance bits model W _ Q weights n le_rfl

noncomputable def weights {n : ℕ} (o : GeneralPaperReducedValuesDriver.Output n) : Fin o.classified.light.size → ℕ :=
  fun j => o.firstWeights.read (index o.classified.light j)

def Conserved {n : ℕ} (o : GeneralPaperReducedValuesDriver.Output n) : Prop :=
  (∑ j,weights o j)=o.classified.lightWeight

theorem reduced_sum {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (w : FixedArrayTable n ℕ) :
    Conserved (GeneralPaperReducedValuesDriver.run bits model W k Q w).1 := by
  rw [GeneralPaperReducedValuesDriver.data]
  unfold GeneralPaperReducedValuesDriver.specification
  split_ifs <;> exact classified_sum bits model W k Q w

theorem original_sum {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ) :
    Conserved (GeneralPaperOriginalValueReduction.run bits model W k values).1 := by
  rw [GeneralPaperOriginalValueReduction.data]
  exact reduced_sum bits model W k _ _

theorem original_positive {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    ∀ j,0<weights (GeneralPaperOriginalValueReduction.run bits model W k values).1 j := by
  have hp := (GeneralPaperValueRoundingPaperContract.positivity bits model W 256 k (by decide) values v hv).2
  intro j
  unfold weights
  rw [(GeneralPaperOriginalValueReduction.retained bits model W k values).1]
  exact hp _

theorem original_total_positive {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (hg : 0<(GeneralPaperOriginalValueReduction.run bits model W k values).1.classified.light.size) :
    0<(GeneralPaperOriginalValueReduction.run bits model W k values).1.classified.lightWeight := by
  have hs := original_sum bits model W k values
  have hp := original_positive bits model W k values v hv
  have h := Finset.sum_pos (fun j _ => hp j) ⟨⟨0,hg⟩,Finset.mem_univ _⟩
  rw [hs] at h
  exact h

theorem original_reconstruct_feasible {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (hg : 0<(GeneralPaperOriginalValueReduction.run bits model W k values).1.classified.light.size)
    (kept : Allocation (GeneralPaperOriginalValueReduction.run bits model W k values).1.classified.heavy.size)
    (x : Fin (GeneralPaperLightFieldReduction.representatives k) → ℝ) (hx : Monotone x) (B : ℝ)
    (hRow : Feasible B (Fin.addCases kept x)) (shift : ℕ) :
    Feasible B (GeneralPaperCircleHardBudget.reconstruct (GeneralPaperLightFieldReduction.representatives k)
      (GeneralPaperOriginalValueReduction.run bits model W k values).1.classified.lightWeight
      (GeneralPaperLightFieldReduction.representatives_positive k)
      (original_total_positive bits model W k values v hv hg)
      (weights (GeneralPaperOriginalValueReduction.run bits model W k values).1) kept x shift) := by
  exact GeneralPaperCircleHardBudget.reconstruct_feasible _ _ _ _ _ (original_sum bits model W k values) kept x hx B hRow shift

end Blotto.GeneralPaperCircleActualWeights
