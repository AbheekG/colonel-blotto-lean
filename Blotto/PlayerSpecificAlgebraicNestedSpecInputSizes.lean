import Blotto.PlayerSpecificAlgebraicNestedSpecInput

/-! Sorting only reuses rows. Endpoint reduction adds one actual field
constant and therefore only one coefficient-height layer. -/
namespace Blotto.PlayerSpecificAlgebraicNestedSpecInputSizes
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicNestedInput
open PlayerSpecificAlgebraicNestedParameterSizes PlayerSpecificAlgebraicNestedSpecInput
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false

theorem sorted_fits (root : Candidate) (a : Input) (ordered : Bool) (T : ℕ) (h : Fits root a T) :
    Fits root (sorted a ordered) T := by
  unfold sorted
  split
  · exact h
  · exact ⟨h.budget,h.second,h.first,h.long,h.short,h.probability⟩

theorem endpoint_fits (root : Candidate) (a : Input) (useShort : Bool) (T : ℕ) (h : Fits root a T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 1 ≤ T) :
    PlayerSpecificAlgebraicThreeEnvironmentSizes.Fits root (endpoint root a useShort) (step T) := by
  have hi : T ≤ step T := (Nat.le_succ _).trans (large T)
  refine ⟨⟨h.budget.1,mono h.budget.2 hi⟩,⟨h.first.1,mono h.first.2 hi⟩,⟨h.second.1,mono h.second.2 hi⟩,?_,?_⟩
  · change Reduced root.polynomial (if useShort then a.short else a.long) ∧ HasHeight (if useShort then a.short else a.long) (step T)
    split
    · exact ⟨h.short.1,mono h.short.2 hi⟩
    · exact ⟨h.long.1,mono h.long.2 hi⟩
  · exact ⟨PlayerSpecificAlgebraicField.constant_reduced _ _ hm hm0,
      constant_height root.polynomial 1 T hmT (one_height.mono hT) hT hml⟩

end Blotto.PlayerSpecificAlgebraicNestedSpecInputSizes
