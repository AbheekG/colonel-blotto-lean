import Blotto.PlayerSpecificFourSpecInputExecution

/-! Complete original-input price for the stable three-length sort,
six copied source rows, six selected rows and retained permutation. -/
namespace Blotto.PlayerSpecificFourSpecInputSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicFourSpecInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (T : ℕ) : ℕ :=
  PlayerSpecificSortTripleSourceCost.coefficient*(T+2)^3+
  (2609*PlayerSpecificResourceCostProfile.rationalCoefficient)*(T+7)^3+2

theorem source_bounds (root : Candidate) (a : Input) (T : ℕ) (ha : Fits root a T) :
    ∀ j, Reduced root.polynomial ((PlayerSpecificFourSpecInputExecution.environment a).read j) ∧
      HasHeight ((PlayerSpecificFourSpecInputExecution.environment a).read j) T := by
  intro j
  fin_cases j <;> simp only [PlayerSpecificFourSpecInputExecution.environment,FixedArrayTable.read_ofFn]
  · exact ha.budget
  · exact ha.lengths 0
  · exact ha.lengths 1
  · exact ha.lengths 2
  · exact ha.mixtureLength
  · exact ha.probability

theorem cost (root : Candidate) (a : Input) (T : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ [])
    (hml : root.polynomial.length ≤ 4) (hmT : HasHeight root.polynomial T)
    (he : HasHeight [root.interval.lo,root.interval.hi] T)
    (hv : root.interval.lo < root.interval.hi) (hT : 2 ≤ T)
    (ha : Fits root a T) :
    (PlayerSpecificFourSpecInputExecution.run root a).2 ≤ work T := by
  let model := RationalCostModel.schoolbook
  let U := T+6
  let W := PlayerSpecificAlgebraicComparisonExecution.width U
  let sorted := PlayerSpecificSortTripleExecution.run root a.lengths
  let result := PlayerSpecificFourSpecInputExecution.selected a sorted.1
  let output := PlayerSpecificAlgebraicFourInput.environment result.input
  let input := PlayerSpecificFourSpecInputExecution.environment a
  have hs := PlayerSpecificSortTripleSourceCost.cost root a.lengths T hm hm0 hml hmT he hv hT ha.lengths
  have hfit : PlayerSpecificAlgebraicFourInput.Fits root result.input T := by
    change PlayerSpecificAlgebraicFourInput.Fits root (PlayerSpecificFourSpecInputExecution.run root a).1.input T
    rw [PlayerSpecificFourSpecInputExecution.value]
    exact PlayerSpecificAlgebraicFourSpecInput.fits model root a T ha
  have hinput : ∀ j, Reduced root.polynomial (input.read j) ∧ HasHeight (input.read j) T :=
    source_bounds root a T ha
  have houtput : ∀ j, Reduced root.polynomial (output.read j) ∧ HasHeight (output.read j) T :=
    PlayerSpecificAlgebraicFourInput.environment_bounds root result.input T hfit
  have hf := PlayerSpecificExpressionVectorFrameCost.cost model root input output U
    (mono hmT (by dsimp [U]; omega)) hml (mono he (by dsimp [U]; omega))
    (fun j => ⟨mono (hinput j).2 (by dsimp [U]; omega),by have h := (hinput j).1.2; omega⟩)
    (fun j => ⟨mono (houtput j).2 (by dsimp [U]; omega),by have h := (houtput j).1.2; omega⟩)
    (by dsimp [U]; omega) (by dsimp [U]; omega) (by dsimp [U]; omega)
  have hf' : price model (PlayerSpecificExpressionVectorExecution.frame root input output) ≤
      (2600*PlayerSpecificResourceCostProfile.rationalCoefficient)*(U+1)^3 :=
    hf.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 2600 U)
  have hw : ∀ word ∈ List.ofFn (fun j : Fin 3 => (result.permutation j).val),
      binaryWordWidth word ≤ W := by
    intro word hword
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hword
    exact (control_width _).trans
      ((Nat.add_le_add_right (by dsimp [U]; have h := (result.permutation j).isLt; omega :
        (result.permutation j).val ≤ U) 1).trans
        (PlayerSpecificAlgebraicActiveListCost.width_large U).2.2)
  have hwords := PlayerSpecificAlgebraicCallerFrame.controls_cost model
    (List.ofFn (fun j : Fin 3 => (result.permutation j).val)) W hw
    (by have h := (PlayerSpecificAlgebraicActiveListCost.width_large U).1; omega)
  have hwords' : price model (List.ofFn (fun j : Fin 3 => Event.control (result.permutation j).val)) ≤
      (9*PlayerSpecificResourceCostProfile.rationalCoefficient)*(U+1)^3 := by
    change price model ((List.ofFn (fun j : Fin 3 => (result.permutation j).val)).map Event.control) ≤ _
    simpa only [List.length_ofFn] using
      hwords.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 9 U)
  change sorted.2 + price model (PlayerSpecificFourSpecInputExecution.frame root a result) +
    price model [.control 1] ≤ _
  rw [PlayerSpecificFourSpecInputExecution.frame,price_append,
    show price model [.control 1] = 2 by rfl]
  have hsum := Nat.add_le_add_right (Nat.add_le_add hs (Nat.add_le_add hf' hwords')) 2
  apply hsum.trans_eq
  dsimp only [U]
  unfold work
  ring

theorem same_return_and_cost (root : Candidate) (a : Input) (T : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ [])
    (hml : root.polynomial.length ≤ 4) (hmT : HasHeight root.polynomial T)
    (he : HasHeight [root.interval.lo,root.interval.hi] T)
    (hv : root.interval.lo < root.interval.hi) (hT : 2 ≤ T)
    (ha : Fits root a T) :
    (PlayerSpecificFourSpecInputExecution.run root a).1 =
      prepare RationalCostModel.schoolbook root a ∧
    (PlayerSpecificFourSpecInputExecution.run root a).2 ≤ work T :=
  ⟨PlayerSpecificFourSpecInputExecution.value root a,
    cost root a T hm hm0 hml hmT he hv hT ha⟩

end Blotto.PlayerSpecificFourSpecInputSourceCost
