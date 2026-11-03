import Blotto.PlayerSpecificSortTripleExecution

/-! Original-height cubic price for the three executed stable-sort
comparisons, complete input/output array frame, and permutation words. -/
namespace Blotto.PlayerSpecificSortTripleSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ :=
  3*PlayerSpecificAlgebraicComparisonCost.comparisonCoefficient+
  1412*PlayerSpecificResourceCostProfile.rationalCoefficient+8

theorem cost (root : Candidate) (a : FixedArrayTable 3 Data) (T : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ [])
    (hml : root.polynomial.length ≤ 4) (hmT : HasHeight root.polynomial T)
    (he : HasHeight [root.interval.lo,root.interval.hi] T)
    (hv : root.interval.lo < root.interval.hi) (hT : 2 ≤ T)
    (ha : ∀ j, Reduced root.polynomial (a.read j) ∧ HasHeight (a.read j) T) :
    (PlayerSpecificSortTripleExecution.run root a).2 ≤ coefficient*(T+2)^3 := by
  let model := RationalCostModel.schoolbook
  let U := T+1
  let first := PlayerSpecificSortTripleExecution.compare root a 0 1
  let M := PlayerSpecificAlgebraicPermutation.permute first.1 a
  let second := PlayerSpecificSortTripleExecution.compare root M 1 2
  let N := PlayerSpecificAlgebraicPermutation.permute second.1 M
  let third := PlayerSpecificSortTripleExecution.compare root N 0 1
  let p := (third.1.trans second.1).trans first.1
  let out := PlayerSpecificAlgebraicPermutation.permute p a
  let W := PlayerSpecificAlgebraicComparisonExecution.width U
  have hM := PlayerSpecificAlgebraicPermutation.bounds root first.1 a T ha
  have hN := PlayerSpecificAlgebraicPermutation.bounds root second.1 M T hM
  have hOut : ∀ j, Reduced root.polynomial (out.read j) ∧ HasHeight (out.read j) T :=
    PlayerSpecificAlgebraicPermutation.bounds root p a T ha
  have hcomp (b : FixedArrayTable 3 Data) (hb : ∀ j, Reduced root.polynomial (b.read j) ∧ HasHeight (b.read j) T)
      (i j : Fin 3) :
      (PlayerSpecificSortTripleExecution.compare root b i j).2 ≤
        PlayerSpecificAlgebraicComparisonCost.comparisonCoefficient*(T+1)^3+2 := by
    have h := PlayerSpecificAlgebraicComparisonCost.comparison root (b.read i) (b.read j) T
      hm hm0 hml hmT he hv (hb i).2 (hb j).2
      (by have hr := (hb i).1.2; omega) (by have hr := (hb j).1.2; omega) (by omega)
    change (PlayerSpecificAlgebraicComparisonExecution.run model root (b.read i) (b.read j)).2+
      price model [.control 1] ≤ _
    rw [show price model [.control 1] = 2 by rfl]
    simpa only [model] using Nat.add_le_add_right h 2
  have hfirst := hcomp a ha 0 1
  have hsecond := hcomp M hM 1 2
  have hthird := hcomp N hN 0 1
  have hf := PlayerSpecificExpressionVectorFrameCost.cost model root a out U
    (mono hmT (by dsimp [U]; omega)) hml (mono he (by dsimp [U]; omega))
    (fun j => ⟨mono (ha j).2 (by dsimp [U]; omega),by have h := (ha j).1.2; omega⟩)
    (fun j => ⟨mono (hOut j).2 (by dsimp [U]; omega),by have h := (hOut j).1.2; omega⟩)
    (by dsimp [U]; omega) (by dsimp [U]; omega) (by dsimp [U]; omega)
  have hf' : price model (PlayerSpecificExpressionVectorExecution.frame root a out) ≤
      (1400*PlayerSpecificResourceCostProfile.rationalCoefficient)*(U+1)^3 :=
    hf.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 1400 U)
  have hw : ∀ word ∈ List.ofFn (fun j : Fin 3 => (p j).val), binaryWordWidth word ≤ W := by
    intro word hword
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hword
    have hj := (p j).isLt
    exact (control_width _).trans
      ((Nat.add_le_add_right (by dsimp [U]; omega : (p j).val ≤ U) 1).trans
        (PlayerSpecificAlgebraicActiveListCost.width_large U).2.2)
  have hwords := PlayerSpecificAlgebraicCallerFrame.controls_cost model
    (List.ofFn (fun j : Fin 3 => (p j).val)) W hw
    (by have h := (PlayerSpecificAlgebraicActiveListCost.width_large U).1; omega)
  have hwords' : price model (List.ofFn (fun j : Fin 3 => Event.control (p j).val)) ≤
      (9*PlayerSpecificResourceCostProfile.rationalCoefficient)*(U+1)^3 := by
    change price model ((List.ofFn (fun j : Fin 3 => (p j).val)).map Event.control) ≤ _
    simpa only [List.length_ofFn] using
      hwords.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 9 U)
  change first.2+second.2+third.2+price model (PlayerSpecificSortTripleExecution.frame root a out p)+
    price model [.control 1] ≤ _
  rw [PlayerSpecificSortTripleExecution.frame,price_append,
    show price model [.control 1] = 2 by rfl]
  have hsum := Nat.add_le_add_right
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hfirst hsecond) hthird)
      (Nat.add_le_add hf' hwords')) 2
  have hpow : (T+1)^3 ≤ (U+1)^3 := by
    dsimp [U]
    exact Nat.pow_le_pow_left (by omega) 3
  have hcmpbound := Nat.mul_le_mul_left
    (3*PlayerSpecificAlgebraicComparisonCost.comparisonCoefficient) hpow
  dsimp only [U] at hcmpbound
  rw [show T+1+1=T+2 by omega] at hcmpbound
  apply hsum.trans
  calc
    _ = (3*PlayerSpecificAlgebraicComparisonCost.comparisonCoefficient)*(T+1)^3+
        (1409*PlayerSpecificResourceCostProfile.rationalCoefficient)*(T+2)^3+8 := by
          dsimp only [U]
          ring
    _ ≤ (3*PlayerSpecificAlgebraicComparisonCost.comparisonCoefficient)*(T+2)^3+
        (1409*PlayerSpecificResourceCostProfile.rationalCoefficient)*(T+2)^3+8 := by omega
    _ ≤ coefficient*(T+2)^3 := by
      unfold coefficient
      have hpositive : 1 ≤ (T+2)^3 := Nat.succ_le_of_lt (pow_pos (by omega) 3)
      nlinarith only [hpositive,
        Nat.zero_le (PlayerSpecificResourceCostProfile.rationalCoefficient*(T+2)^3)]

theorem same_return_and_cost (root : Candidate) (a : FixedArrayTable 3 Data) (T : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ [])
    (hml : root.polynomial.length ≤ 4) (hmT : HasHeight root.polynomial T)
    (he : HasHeight [root.interval.lo,root.interval.hi] T)
    (hv : root.interval.lo < root.interval.hi) (hT : 2 ≤ T)
    (ha : ∀ j, Reduced root.polynomial (a.read j) ∧ HasHeight (a.read j) T) :
    (PlayerSpecificSortTripleExecution.run root a).1 =
      PlayerSpecificAlgebraicSortTriple.prepare RationalCostModel.schoolbook root a ∧
    (PlayerSpecificSortTripleExecution.run root a).2 ≤ coefficient*(T+2)^3 :=
  ⟨PlayerSpecificSortTripleExecution.value root a,
    cost root a T hm hm0 hml hmT he hv hT ha⟩

end Blotto.PlayerSpecificSortTripleSourceCost
