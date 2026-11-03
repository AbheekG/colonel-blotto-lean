import Blotto.PlayerSpecificAlgebraicThreeEnvironmentSizes

/-! A reusable proof-only size interface for actual cached segment rows. -/
namespace Blotto.PlayerSpecificAlgebraicDescriptorBounds
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificAlgebraicReduction
open PlayerSpecificAlgebraicCandidates (Candidate)
open PlayerSpecificAlgebraicSegment
set_option autoImplicit false

structure Bounds {N slots : ℕ} (root : Candidate) (d : Descriptor N slots) (T : ℕ) : Prop where
  weights : ∀ slot,Reduced root.polynomial (d.weights.read slot) ∧ HasHeight (d.weights.read slot) T
  first : ∀ slot j,Reduced root.polynomial ((d.first.read slot).read j) ∧ HasHeight ((d.first.read slot).read j) T
  second : ∀ slot j,Reduced root.polynomial ((d.second.read slot).read j) ∧ HasHeight ((d.second.read slot).read j) T

end Blotto.PlayerSpecificAlgebraicDescriptorBounds
