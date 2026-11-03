import Blotto.GeneralPaperStoredCirclePreparationPrice

/-! Materialize original light weights from retained first weights and
original index arrays once. The sum/positivity bounds below are erased
observations of that return; no input reduction or weight-sum pass replays. -/
namespace Blotto.GeneralPaperNativeLightWeights
open GeneralPaperLightFieldOrder
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

def run {n : ℕ} (indexCost : ℕ → ℕ) (A : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) :
    FixedArrayTable o.classified.light.size ℕ×ℕ :=
  PaperIndexedArrayConstruction.run indexCost A (fun j => (o.firstWeights.read (index o.classified.light j),64*A))

theorem data {n : ℕ} (indexCost : ℕ → ℕ) (A : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) :
    (run indexCost A o).1=FixedArrayTable.ofFn (GeneralPaperCircleActualWeights.weights o) := by
  unfold run
  rw [PaperIndexedArrayConstruction.run_data]
  rfl

theorem models_data {n : ℕ} (indexCost indexCost' : ℕ → ℕ) (A A' : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) :
    (run indexCost A o).1=(run indexCost' A' o).1 := by rw [data,data]

theorem work {n : ℕ} (indexCost : ℕ → ℕ) (A : ℕ) (hA : 1≤A) (o : GeneralPaperReducedValuesDriver.Output n)
    (hIndex : ∀ i≤o.classified.light.size,indexCost (binaryWordWidth (i+1))≤A) :
    (run indexCost A o).2≤o.classified.light.size*(64*A)+44*(o.classified.light.size+1)*A := by
  unfold run
  exact GeneralPaperControlArrayPrice.indexed_work indexCost A (64*A) _ hA hIndex (fun _ => le_rfl)

theorem arithmetic_work {n : ℕ} (o : GeneralPaperReducedValuesDriver.Output n) :
    (run (fun _ => 1) 1 o).2≤108*o.classified.light.size+44 := by
  have h := work (fun _ => 1) 1 (by decide) o (fun _ _ => le_rfl)
  nlinarith only [h]

theorem original_sum {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (input : FixedArrayTable n ℚ)
    (indexCost : ℕ → ℕ) (A : ℕ) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
    (∑ j,(run indexCost A o).1.read j)=o.classified.lightWeight := by
  dsimp only
  rw [data]
  simp only [FixedArrayTable.read_ofFn]
  exact GeneralPaperCircleActualWeights.original_sum bits model W k input

theorem original_positive {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (input : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,input.read j=v.weight j) (indexCost : ℕ → ℕ) (A : ℕ) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
    ∀ j,0<(run indexCost A o).1.read j := by
  dsimp only
  rw [data]
  simp only [FixedArrayTable.read_ofFn]
  exact GeneralPaperCircleActualWeights.original_positive bits model W k input v hv

theorem original_bounded {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (input : FixedArrayTable n ℚ)
    (indexCost : ℕ → ℕ) (A : ℕ) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
    ∀ j,(run indexCost A o).1.read j≤o.classified.lightWeight := by
  dsimp only
  rw [← original_sum bits model W k input indexCost A]
  intro j
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

end Blotto.GeneralPaperNativeLightWeights
