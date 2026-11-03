import Blotto.PlayerSpecificCubic

/-! Cubic roots are equivalent to the two mean equations on each ratio
cell. The recovered scale is positive for positive input, including the
unbounded outer cells. These are recognition components, not a root oracle. -/
namespace Blotto.PlayerSpecificCandidate
open scoped BigOperators
open PlayerSpecificCubic
set_option autoImplicit false
set_option maxHeartbeats 2500000
variable {𝕂 : Type*} [Field 𝕂] [LinearOrder 𝕂] [IsStrictOrderedRing 𝕂]

theorem algebra (c : Coefficients 𝕂) (b gamma scale : 𝕂) (hb : 0<b) (hg : 0<gamma) :
    (2*scale=gamma*c.A1+c.A2/gamma ∧ 2*b*scale=gamma^2*c.B1+c.B2) ↔
      cubic c b gamma=0 ∧ scale=candidateScale c b gamma := by
  constructor
  · rintro ⟨hA,hB⟩
    field_simp [hg.ne'] at hA
    constructor
    · unfold cubic
      linear_combination b*hA-gamma*hB
    · unfold candidateScale
      apply (eq_div_iff (mul_pos (by norm_num : (0 : 𝕂)<2) hb).ne').mpr
      linear_combination hB
  · rintro ⟨hc,hs⟩
    have hB : 2*b*scale=gamma^2*c.B1+c.B2 := by
      rw [hs]
      unfold candidateScale
      field_simp [hb.ne']
    refine ⟨?_,hB⟩
    field_simp [hg.ne']
    apply mul_left_cancel₀ hb.ne'
    unfold cubic at hc
    linear_combination gamma*hB+hc

theorem B1_nonnegative {n : ℕ} (v w : Fin n → 𝕂) (high : Fin n → Bool) (hv : ∀ j,0<v j) :
    0≤(coefficients v w high).B1 := by
  change 0≤∑ j,if high j then (w j)^2/v j else 0
  apply Finset.sum_nonneg
  intro j _
  split
  · exact div_nonneg (sq_nonneg _) (hv j).le
  · exact le_rfl

theorem B2_nonnegative {n : ℕ} (v w : Fin n → 𝕂) (high : Fin n → Bool) (hv : ∀ j,0<v j) :
    0≤(coefficients v w high).B2 := by
  change 0≤∑ j,if high j then 0 else v j
  apply Finset.sum_nonneg
  intro j _
  split
  · exact le_rfl
  · exact (hv j).le

theorem nonzero_coefficients {n : ℕ} (v w : Fin n → 𝕂) (high : Fin n → Bool)
    (hn : 0<n) (hv : ∀ j,0<v j) (hw : ∀ j,0<w j) :
    0<(coefficients v w high).B1 ∨ 0<(coefficients v w high).B2 := by
  let j : Fin n := ⟨0,hn⟩
  cases hh : high j with
  | false =>
    right
    have hSingle : (if high j then 0 else v j)≤(coefficients v w high).B2 := by
      change (if high j then 0 else v j)≤∑ l,if high l then 0 else v l
      exact Finset.single_le_sum (f := fun l : Fin n => if high l then 0 else v l) (fun l _ => by split; exact le_rfl; exact (hv l).le) (Finset.mem_univ j)
    exact (hv j).trans_le (by simpa only [hh,Bool.false_eq_true,ite_false] using hSingle)
  | true =>
    left
    have hSingle : (if high j then (w j)^2/v j else 0)≤(coefficients v w high).B1 := by
      change (if high j then (w j)^2/v j else 0)≤∑ l,if high l then (w l)^2/v l else 0
      exact Finset.single_le_sum (f := fun l : Fin n => if high l then (w l)^2/v l else 0) (fun l _ => by split; exact div_nonneg (sq_nonneg _) (hv l).le; exact le_rfl) (Finset.mem_univ j)
    exact (div_pos (sq_pos_of_pos (hw j)) (hv j)).trans_le (by simpa only [hh,ite_true] using hSingle)

theorem scale_positive {n : ℕ} (v w : Fin n → 𝕂) (high : Fin n → Bool) (b gamma : 𝕂)
    (hn : 0<n) (hv : ∀ j,0<v j) (hw : ∀ j,0<w j) (hb : 0<b) (hg : 0<gamma) :
    0<candidateScale (coefficients v w high) b gamma := by
  unfold candidateScale
  apply div_pos _ (mul_pos (by norm_num) hb)
  rcases nonzero_coefficients v w high hn hv hw with h | h
  · exact add_pos_of_pos_of_nonneg (mul_pos (sq_pos_of_pos hg) h) (B2_nonnegative v w high hv)
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (sq_nonneg _) (B1_nonnegative v w high hv)) h

theorem root_iff_means {n : ℕ} (v w : Fin n → 𝕂) (high : Fin n → Bool) (b gamma scale : 𝕂)
    (hv : ∀ j,0<v j) (hw : ∀ j,0<w j) (hb : 0<b) (hg : 0<gamma) (hs : 0<scale)
    (h : Respects v w high gamma) :
    ((∑ j,PlayerSpecificMarginals.probA (v j) (w j) gamma*PlayerSpecificMarginals.length (v j) (w j) gamma scale)=2 ∧
      (∑ j,PlayerSpecificMarginals.probB (v j) (w j) gamma*PlayerSpecificMarginals.length (v j) (w j) gamma scale)=2*b) ↔
      cubic (coefficients v w high) b gamma=0 ∧ scale=candidateScale (coefficients v w high) b gamma :=
  (mean_equations v w high b gamma scale hv hw hg hs h).trans (algebra _ b gamma scale hb hg)

theorem candidate_means {n : ℕ} (v w : Fin n → 𝕂) (high : Fin n → Bool) (b gamma : 𝕂)
    (hn : 0<n) (hv : ∀ j,0<v j) (hw : ∀ j,0<w j) (hb : 0<b) (hg : 0<gamma)
    (h : Respects v w high gamma) (hc : cubic (coefficients v w high) b gamma=0) :
    let scale := candidateScale (coefficients v w high) b gamma
    (∑ j,PlayerSpecificMarginals.probA (v j) (w j) gamma*PlayerSpecificMarginals.length (v j) (w j) gamma scale)=2 ∧
      (∑ j,PlayerSpecificMarginals.probB (v j) (w j) gamma*PlayerSpecificMarginals.length (v j) (w j) gamma scale)=2*b :=
  (root_iff_means v w high b gamma _ hv hw hb hg (scale_positive v w high b gamma hn hv hw hb hg) h).mpr ⟨hc,rfl⟩

end Blotto.PlayerSpecificCandidate
