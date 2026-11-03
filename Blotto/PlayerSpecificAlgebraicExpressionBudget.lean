import Blotto.PlayerSpecificAlgebraicExpressionValue

/-! Depth monotonicity and a common one-operation height envelope for
fixed local algebraic programs. These are proof-only analysis bounds. -/
namespace Blotto.PlayerSpecificAlgebraicExpressionBudget
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem fuel_mono (H : ℕ) : Monotone (fun k => iterate k H) := by
  apply monotone_nat_of_le_succ
  intro k
  exact (Nat.le_succ _).trans (large (iterate k H))

theorem initial_le (k H : ℕ) : H≤ iterate k H := fuel_mono H (Nat.zero_le k)

def height {k : ℕ} (e : RationalExpression k) (H : ℕ) : ℕ := iterate (e.depth+1) H

theorem depth_mono (H : ℕ) {a b : ℕ} (h : a≤b) : iterate (a+1) H≤ iterate (b+1) H :=
  fuel_mono H (Nat.add_le_add_right h 1)

theorem linear {k : ℕ} (e : RationalExpression k) (H : ℕ) :
    height e H+1≤(PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^(e.depth+1)*(H+1) := iterate_bound _ _

theorem binary_heights (model : RationalCostModel) (root : Candidate) (a b : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (ha : Reduced root.polynomial a) (hb : Reduced root.polynomial b)
    (hmH : HasHeight root.polynomial H) (haH : HasHeight a H) (hbH : HasHeight b H) (hH : 1≤H) :
    HasHeight (PlayerSpecificAlgebraicField.plus root.polynomial a b) (step H) ∧
      HasHeight (PlayerSpecificAlgebraicField.minus root.polynomial a b) (step H) ∧
      HasHeight (PlayerSpecificAlgebraicField.times root.polynomial a b) (step H) ∧
      HasHeight (PlayerSpecificAlgebraicField.divide root.polynomial a b) (step H) ∧
      HasHeight (if PlayerSpecificAlgebraicPairStep.le model root a b then a else b) (step H) ∧
      HasHeight (if PlayerSpecificAlgebraicPairStep.le model root a b then b else a) (step H) := by
  have hshort : H+H+1≤step H := by
    have h:=calibrate 3 H (by unfold PlayerSpecificAlgebraicHeightEnvelope.coefficient; omega)
    omega
  have hinc : H≤step H := (Nat.le_succ _).trans (large H)
  refine ⟨mono (PlayerSpecificShortReduction.plus_height _ _ _ hm hm0 ha hb H H haH hbH) hshort,
    mono (PlayerSpecificShortReduction.minus_height _ _ _ hm hm0 ha hb H H haH hbH) hshort,
    times_height _ _ _ H hm hm0 hml ha hb hmH haH hbH,
    divide_height _ _ _ H hm hm0 hml ha hb hmH haH hbH hH,?_,?_⟩
  · split
    · exact mono haH hinc
    · exact mono hbH hinc
  · split
    · exact mono hbH hinc
    · exact mono haH hinc

end Blotto.PlayerSpecificAlgebraicExpressionBudget
