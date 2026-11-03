import Blotto.PlayerSpecificAlgebraicInitialInputSizes

/-! Computed positive field values have a dyadic lower bound of polynomial
precision. The bound uses the actual Bezout unit row and selected-root
enclosure, with no norm, sign or minimum-length oracle. -/
namespace Blotto.PlayerSpecificPositiveFieldLowerBound
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificSturmVariations PlayerSpecificIsolationState
set_option autoImplicit false
set_option maxHeartbeats 2500000

def dyadic (s : ℕ) : ℚ := 1/(2:ℚ)^s
def exponent (m a : Data) (node : Interval) : ℕ :=
  binaryWordWidth (PlayerSpecificAlgebraicSignMagnitude.gapDenominator m a (PlayerSpecificSignEnclosure.magnitude node))
def coefficient : ℕ := 33*(68*PlayerSpecificExtendedGCDHeights.linearConstant+18)+200

theorem dyadic_positive (s : ℕ) : 0<dyadic s := div_pos (by norm_num) (pow_pos (by norm_num) _)

theorem dyadic_le_inverse (B : ℕ) (hB : 0<B) : ((dyadic (binaryWordWidth B)):ℝ)≤(1:ℝ)/(B:ℝ) := by
  have hb : (0:ℝ)<(B:ℝ) := by exact_mod_cast hB
  have hp : (B:ℝ)≤(2:ℝ)^binaryWordWidth B := by exact_mod_cast (lt_pow_binaryWordWidth B).le
  simpa only [dyadic,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using one_div_le_one_div_of_le hb hp

theorem positive_lower_bound (m a : Data) (node : Interval) (hm : Normalized m)
    (hirr : Irreducible (semantics m)) (ha : Reduced m a) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique m node x) (hpos : 0<realEvaluate a x) :
    ((dyadic (exponent m a node)):ℝ)≤realEvaluate a x := by
  have hm0 : m≠[] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  have ha0 : a≠[] := by intro hz; subst a; exact (lt_irrefl (0:ℝ)) hpos
  have hp:=PlayerSpecificPolynomialNormalization.nonzero a ha.1 ha0
  have hd:=degree_lt m a hm hm0 ha hp
  have hg:=PlayerSpecificAlgebraicSignMagnitude.gap m a hirr hp hd
    (PlayerSpecificSignEnclosure.magnitude node) x hx.1 (PlayerSpecificSignEnclosure.inside_bound node x hx.2.1)
  rw [abs_of_pos hpos] at hg
  exact (dyadic_le_inverse _ (PlayerSpecificAlgebraicSignMagnitude.gap_positive m a _)).trans hg

theorem width_profile (C H S E B : ℕ) (hS : S≤32*(H+1)) (hE : E≤5*(H+1))
    (hB : B≤C*(S+1)+17*E+36) : B≤(33*C+200)*(H+1) := by
  have hs : S+1≤33*(H+1) := by omega
  have hm:=Nat.mul_le_mul_left C hs
  nlinarith only [hE,hB,hm]

theorem polynomial_precision (m a : Data) (node : Interval) (H : ℕ)
    (hm : HasHeight m H) (ha : HasHeight a H) (he : HasHeight [node.lo,node.hi] H)
    (hml : m.length≤4) (hal : a.length≤3) : exponent m a node≤coefficient*(H+1) := by
  have hi:=PlayerSpecificCandidateTestBudget.encoded_input m a node H hm ha he hml (by omega)
  have hc:=PlayerSpecificSignLinearSizes.certificate_bounds m a node hml hal
  have hg:=PlayerSpecificSignDepthHeights.gap_width m a node hc.1
  have heHeight:=inputHeight_le he
  have heCap : PlayerSpecificSignEnclosure.endpointHeight node≤5*(H+1) := by
    simp only [List.length_cons,List.length_nil] at heHeight
    exact heHeight.trans (by omega)
  have hb : exponent m a node≤(68*PlayerSpecificExtendedGCDHeights.linearConstant+18)*
      (PlayerSpecificSignLinearSizes.inputHeight m a node+1)+17*PlayerSpecificSignEnclosure.endpointHeight node+36 := by
    unfold exponent
    omega
  exact width_profile (68*PlayerSpecificExtendedGCDHeights.linearConstant+18) H _ _ _ hi heCap hb

end Blotto.PlayerSpecificPositiveFieldLowerBound
