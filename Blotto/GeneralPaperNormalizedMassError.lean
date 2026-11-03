import Blotto.GeneralPaperMassApproximation

/-! Relative downward mass errors give the paper's normalized comparison
error. The exact scaled dyadic comparator then preserves quantile bracket
inequalities even when the sequence of rounded queries is not monotone.
-/
namespace Blotto.GeneralPaperNormalizedMassError
open GeneralPaperDyadicFloat
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem normalized_error (P T a t error : ℝ) (hT : 0<T) (hP : 0≤P) (hPT : P≤T)
    (hError : 0≤error) (hOne : error<1)
    (ha : (1-error)*P≤a ∧ a≤P) (ht : (1-error)*T≤t ∧ t≤T) :
    |a/t-P/T|≤2*error/(1-error) := by
  have hDen : 0<(1-error)*T := mul_pos (by linarith) hT
  have hPrefix : |a-P|≤error*T := by
    rw [abs_of_nonpos (by linarith [ha.2])]
    have he := mul_le_mul_of_nonneg_left hPT hError
    nlinarith only [ha.1,he]
  have hTotal : |t-T|≤error*T := by
    rw [abs_of_nonpos (by linarith [ht.2])]
    nlinarith only [ht.1]
  have he := GeneralPaperCDFReweighting.normalized_difference a t P T (error*T) (error*T)
    (hDen.trans_le ht.1) hT hP hPT hPrefix hTotal
  have hd := div_le_div_of_nonneg_left (show 0≤error*T+error*T by positivity) hDen ht.1
  calc
    _ ≤ (error*T+error*T)/t := he
    _ ≤ (error*T+error*T)/((1-error)*T) := hd
    _ = _ := by field_simp; ring

def error (k : ℕ) : ℚ := (GeneralPaperSourceParameters.prepare k).nu/64

def delta (k : ℕ) : ℚ := 2*error k/(1-error k)

theorem error_bounds (k : ℕ) : 0<error k ∧ error k<1 := by
  have hp := (GeneralPaperSourceParameters.positive k).2.2.1
  have he := GeneralPaperSourceParameters.eta_upper k
  have hn := GeneralPaperSourceParameters.nu_eta k
  unfold error
  rw [hn]
  constructor <;> linarith

theorem delta_nonnegative (k : ℕ) : 0≤delta k := by
  have he := error_bounds k
  unfold delta
  exact div_nonneg (by linarith) (by linarith)

theorem delta_small (k : ℕ) : delta k<(GeneralPaperSourceParameters.prepare k).nu/16 := by
  have hp := (GeneralPaperSourceParameters.positive k).2.2.1
  have hn : (GeneralPaperSourceParameters.prepare k).nu≤1 := by
    rw [GeneralPaperSourceParameters.nu_eta]
    linarith [GeneralPaperSourceParameters.eta_upper k]
  have he := error_bounds k
  unfold delta
  apply (div_lt_iff₀ (by linarith : (0:ℚ)<1-error k)).mpr
  unfold error
  nlinarith [mul_nonneg (by linarith : (0:ℚ)≤1-(GeneralPaperSourceParameters.prepare k).nu) hp.le]

theorem summary_slack (k : ℕ) :
    1/((GeneralPaperSourceParameters.prepare k).summarySize:ℚ)+delta k<(GeneralPaperSourceParameters.prepare k).nu := by
  have hs := GeneralPaperSourceParameters.summary_exact k
  have hd := delta_small k
  have hp := (GeneralPaperSourceParameters.positive k).2.2.1
  rw [hs]
  have hi : 1/((4:ℚ)/(GeneralPaperSourceParameters.prepare k).nu)=(GeneralPaperSourceParameters.prepare k).nu/4 := by field_simp
  rw [hi]
  linarith

theorem comparison_branches (width j s : ℕ) (storedPrefix storedTotal : Number) (P T error : ℝ)
    (hS : 0<s) (hT : 0<T) (hP : 0≤P) (hPT : P≤T) (hError : 0≤error) (hOne : error<1)
    (hPrefix : (1-error)*P≤(value storedPrefix:ℝ) ∧ (value storedPrefix:ℝ)≤P)
    (hTotal : (1-error)*T≤(value storedTotal:ℝ) ∧ (value storedTotal:ℝ)≤T)
    (hLeft : (GeneralPaperDyadicCompare.scale j storedTotal).mantissa<2^width)
    (hRight : (GeneralPaperDyadicCompare.scale s storedPrefix).mantissa<2^width) :
    ((GeneralPaperDyadicCompare.scaledLE width j storedTotal s storedPrefix).answer=true →
      (j:ℝ)/s-2*error/(1-error)≤P/T) ∧
    ((GeneralPaperDyadicCompare.scaledLE width j storedTotal s storedPrefix).answer=false →
      P/T≤(j:ℝ)/s+2*error/(1-error)) := by
  have hNormalized := normalized_error P T (value storedPrefix:ℝ) (value storedTotal:ℝ) error
    hT hP hPT hError hOne hPrefix hTotal
  have hAbs := abs_le.mp hNormalized
  have hPos : (0:ℝ)<value storedTotal :=
    (mul_pos (by linarith : (0:ℝ)<1-error) hT).trans_le hTotal.1
  have hs : (0:ℝ)<s := by exact_mod_cast hS
  have hCmp := GeneralPaperDyadicCompare.scaled_correct width j storedTotal s storedPrefix hLeft hRight
  constructor
  · intro hChoose
    have hQ := hCmp.mp hChoose
    have hR : (j:ℝ)*(value storedTotal:ℝ)≤(s:ℝ)*(value storedPrefix:ℝ) := by exact_mod_cast hQ
    have hRatio : (j:ℝ)/s≤(value storedPrefix:ℝ)/(value storedTotal:ℝ) := by
      apply (div_le_div_iff₀ hs hPos).mpr
      nlinarith only [hR]
    linarith
  · intro hChoose
    have hNot : ¬(GeneralPaperDyadicCompare.scaledLE width j storedTotal s storedPrefix).answer=true := by rw [hChoose]; decide
    have hQ : (s:ℚ)*value storedPrefix<(j:ℚ)*value storedTotal := lt_of_not_ge (fun h => hNot (hCmp.mpr h))
    have hR : (s:ℝ)*(value storedPrefix:ℝ)<(j:ℝ)*(value storedTotal:ℝ) := by exact_mod_cast hQ
    have hRatio : (value storedPrefix:ℝ)/(value storedTotal:ℝ)<(j:ℝ)/s := by
      apply (div_lt_div_iff₀ hPos hs).mpr
      nlinarith only [hR]
    linarith

end Blotto.GeneralPaperNormalizedMassError
