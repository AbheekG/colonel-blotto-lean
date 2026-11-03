import Blotto.PlayerSpecificAlgebraicThreeGeometrySample
import Blotto.PlayerSpecificAlgebraicSegmentHeights

/-! The entire executed geometric descriptor and midpoint interpolation
have fixed depth. Output coefficient height is linear in the four original
environment heights and midpoint precision, with one global coefficient. -/
namespace Blotto.PlayerSpecificAlgebraicThreeGeometrySizes
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def height (T K : ℕ) : ℕ := iterate 3 (iterate 17 T+2*K+6)
def coefficient : ℕ := (PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^3*
  ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^17+8)

theorem linear (T K : ℕ) : height T K+1≤coefficient*(T+K+1) := by
  have hi:=iterate_bound 17 T
  have ho:=iterate_bound 3 (iterate 17 T+2*K+6)
  have hA : 1≤(PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^17 := Nat.succ_le_of_lt (pow_pos (Nat.succ_pos _) 17)
  have he : iterate 17 T+2*K+6+1≤((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^17+8)*(T+K+1) := by
    nlinarith only [hi,hA,Nat.zero_le T,Nat.zero_le K]
  exact ho.trans (by simpa only [coefficient,mul_assoc] using
    Nat.mul_le_mul_left ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^3) he)

theorem draw_heights (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable 4 Data) (H K : ℕ)
    (bits : Fin (8*H+K) → Bool) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hml : root.polynomial.length≤4) (T : ℕ) (hmT : HasHeight root.polynomial T) (hT : 2≤T)
    (hEnv : ∀ j,Reduced root.polynomial (env.read j) ∧ HasHeight (env.read j) T) :
    ∀ j,HasHeight ((PlayerSpecificAlgebraicThreeGeometrySample.draw model root env H K bits).read j) (height T K) := by
  have hred:=PlayerSpecificAlgebraicThreeGeometry.reduced model root env hm hm0 (fun j => (hEnv j).1)
  have hh:=PlayerSpecificAlgebraicThreeGeometry.heights model root env hm hm0 hml T hmT hT hEnv
  have hm17:=mono hmT (PlayerSpecificAlgebraicExpressionBudget.initial_le 17 T)
  exact PlayerSpecificAlgebraicSegmentHeights.sample model root (PlayerSpecificAlgebraicThreeGeometry.prepare model root env)
    8 H K bits hm hm0 hml (iterate 17 T) hm17 (fun slot j => ⟨hred.2.1 slot j,hh.2.1 slot j⟩)
      (fun slot j => ⟨hred.2.2 slot j,hh.2.2 slot j⟩)

end Blotto.PlayerSpecificAlgebraicThreeGeometrySizes
