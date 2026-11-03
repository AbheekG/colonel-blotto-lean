import Blotto.GeneralPaperBasisAffineEvaluate

/-! Exact affine residuals and sign preservation up to a weak endpoint.
The half-open root condition allows a previously strict inequality to
become tight at the endpoint, including coincident dictionary anchors.
-/
namespace Blotto.GeneralPaperBasisResidualSign
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperBasisCoordinates
open GeneralPaperBasisAffineData GeneralPaperBasisAffineSystem
set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable def residual {m K : ℕ} (r : Row (Variable m K)) (data : Data (m*(K-1))) (gamma : ℝ) : ℝ :=
  r.linear.evaluate (fun a => value data gamma (index a))-r.bound gamma

noncomputable def intercept {m K : ℕ} (r : Row (Variable m K)) (data : Data (m*(K-1))) : ℝ :=
  r.linear.evaluate (fun a => (data.constant.read (index a):ℝ)/(data.determinant:ℝ))-(r.constant:ℝ)

noncomputable def slope {m K : ℕ} (r : Row (Variable m K)) (data : Data (m*(K-1))) : ℝ :=
  r.linear.evaluate (fun a => (data.slope.read (index a):ℝ)/(data.determinant:ℝ))-(r.slope:ℝ)

theorem expansion {m K : ℕ} (r : Row (Variable m K)) (data : Data (m*(K-1))) (gamma : ℝ) :
    residual r data gamma=intercept r data+gamma*slope r data := by
  unfold residual value
  rw [GeneralPaperRayEndpointReal.linear_real]
  unfold intercept slope Row.bound
  ring

theorem affine_nonpositive (a b lo hi : ℝ) (hOrder : lo≤hi) (hStart : a+lo*b≤0)
    (hNoZero : ∀ gamma : ℝ,lo≤gamma ∧ gamma<hi → a+gamma*b≠0) : a+hi*b≤0 := by
  by_contra hn
  have hEnd : 0<a+hi*b := lt_of_not_ge hn
  have hB : 0<b := by
    by_contra hb
    have hh := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hOrder) (le_of_not_gt hb)
    nlinarith only [hStart,hEnd,hh]
  let r := -a/b
  have hl : lo≤r := (le_div_iff₀ hB).mpr (by linarith only [hStart])
  have hr : r<hi := (div_lt_iff₀ hB).mpr (by linarith only [hEnd])
  apply hNoZero r ⟨hl,hr⟩
  dsimp only [r]
  field_simp
  ring

theorem preserves {m K : ℕ} (r : Row (Variable m K)) (data : Data (m*(K-1))) (lo hi : ℝ)
    (hOrder : lo≤hi) (hStart : residual r data lo≤0)
    (hNoZero : ∀ gamma : ℝ,lo≤gamma ∧ gamma<hi → residual r data gamma≠0) : residual r data hi≤0 := by
  rw [expansion] at hStart ⊢
  apply affine_nonpositive _ _ lo hi hOrder hStart
  intro gamma hGamma
  simpa only [expansion] using hNoZero gamma hGamma

end Blotto.GeneralPaperBasisResidualSign
