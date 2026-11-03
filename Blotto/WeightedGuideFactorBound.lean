import Blotto.RejectionScheduleBounds

/-! A supplied small sum of actual local guide errors bounds the actual
whole-tree factor and computed rejection count. Constructing the learner's
local error allocation is a separate obligation. -/

namespace Blotto
open scoped Classical

namespace WeightedGuideTree

def localErrorSum (tree : WeightedGuideTree) : ℝ :=
  (tree.factors.map (fun gamma => gamma - 1)).sum

theorem gamma_list_error_nonnegative (gammas : List ℝ) (h : ∀ gamma ∈ gammas, 1 ≤ gamma) :
    0 ≤ (gammas.map (fun gamma => gamma - 1)).sum := by
  apply List.sum_nonneg
  intro delta hd
  rcases List.mem_map.mp hd with ⟨gamma, hg, rfl⟩
  exact sub_nonneg.mpr (h gamma hg)

theorem gamma_list_product_nonnegative (gammas : List ℝ) (h : ∀ gamma ∈ gammas, 1 ≤ gamma) :
    0 ≤ gammas.prod := by
  apply List.prod_nonneg
  intro gamma hg
  exact le_trans (by norm_num) (h gamma hg)

theorem gamma_list_complement_product (gammas : List ℝ)
    (h : ∀ gamma ∈ gammas, 1 ≤ gamma)
    (hs : (gammas.map (fun gamma => gamma - 1)).sum < 1) :
    gammas.prod * (1 - (gammas.map (fun gamma => gamma - 1)).sum) ≤ 1 := by
  induction gammas with
  | nil => norm_num
  | cons gamma rest ih =>
    have hg := h gamma (by simp)
    have ht : ∀ g ∈ rest, 1 ≤ g := fun g hg => h g (by simp [hg])
    let S := (rest.map (fun g => g - 1)).sum
    have hS0 : 0 ≤ S := gamma_list_error_nonnegative rest ht
    have hsum : gamma - 1 + S < 1 := by simpa only [List.map_cons, List.sum_cons] using hs
    have hS : S < 1 := by linarith
    have he := ih ht hS
    have hp : 0 ≤ rest.prod := gamma_list_product_nonnegative rest ht
    have hlocal : gamma * (1 - (gamma - 1 + S)) ≤ 1 - S := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hlocal hp
    change gamma * rest.prod * (1 - (gamma - 1 + S)) ≤ 1
    have he' : rest.prod * (1 - S) ≤ 1 := he
    nlinarith

theorem gamma_list_product_bound (gammas : List ℝ) (h : ∀ gamma ∈ gammas, 1 ≤ gamma)
    (hs : (gammas.map (fun gamma => gamma - 1)).sum < 1) :
    gammas.prod ≤ 1 / (1 - (gammas.map (fun gamma => gamma - 1)).sum) := by
  apply (le_div_iff₀ (by linarith : 0 < 1 - (gammas.map (fun gamma => gamma - 1)).sum)).mpr
  exact gamma_list_complement_product gammas h hs

theorem factor_error_bound (tree : WeightedGuideTree) (hc : tree.LowerCertified)
    (hs : tree.localErrorSum < 1) : tree.factor ≤ 1 / (1 - tree.localErrorSum) := by
  rw [factor_eq_product]
  exact gamma_list_product_bound tree.factors (tree.factors_ge_one hc) hs

theorem factor_le_eight_sevenths (tree : WeightedGuideTree) (hc : tree.LowerCertified)
    (hs : tree.localErrorSum ≤ 1 / 8) : tree.factor ≤ 8 / 7 := by
  have hS0 : 0 ≤ tree.localErrorSum := gamma_list_error_nonnegative tree.factors (tree.factors_ge_one hc)
  have he := tree.factor_error_bound hc (by linarith)
  have hden : 0 < 1 - tree.localErrorSum := by linarith
  have hb : 1 / (1 - tree.localErrorSum) ≤ (8 / 7 : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    linarith
  exact he.trans hb

theorem factor_lt_two (tree : WeightedGuideTree) (hc : tree.LowerCertified)
    (hs : tree.localErrorSum ≤ 1 / 8) : tree.factor < 2 :=
  lt_of_le_of_lt (tree.factor_le_eight_sevenths hc hs) (by norm_num)

end WeightedGuideTree

theorem rationalFactorCeiling_le_two (factor : ℚ) (hfactor : factor ≤ 2) :
    rationalFactorCeiling factor ≤ 2 := by
  have hd := factor.den_pos
  have hDen : (0 : ℚ) < factor.den := by exact_mod_cast hd
  have hnum : (factor.num : ℚ) ≤ 2 * factor.den := by
    have he := (mul_le_mul_iff_of_pos_right hDen).mpr hfactor
    have hprod : factor * factor.den = (factor.num : ℚ) :=
      ((div_eq_iff (ne_of_gt hDen)).mp factor.num_div_den).symm
    rw [hprod] at he
    exact he
  have hnumInt : factor.num ≤ (2 * factor.den : ℕ) := by exact_mod_cast hnum
  have hnumNat : factor.num.toNat ≤ 2 * factor.den := by omega
  unfold rationalFactorCeiling
  have he : factor.num.toNat + factor.den - 1 < (2 + 1) * factor.den := by omega
  have hlt := (Nat.div_lt_iff_lt_mul hd).mpr he
  omega

namespace RationalWeightedGuideTree

theorem factor_small_error (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (hs : tree.real.localErrorSum ≤ 1 / 8) : tree.factor ≤ 8 / 7 := by
  have he := tree.real.factor_le_eight_sevenths hc hs
  rw [← factor_real] at he
  have he' : (tree.factor : ℝ) ≤ ((8 / 7 : ℚ) : ℝ) := by
    norm_num at *
    exact he
  exact_mod_cast he'

theorem factorCeiling_small_error (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (hs : tree.real.localErrorSum ≤ 1 / 8) : rationalFactorCeiling tree.factor ≤ 2 := by
  apply rationalFactorCeiling_le_two
  have he := tree.factor_small_error hc hs
  linarith

theorem scheduledAttempts_small_error (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (hs : tree.real.localErrorSum ≤ 1 / 8) (E : ℕ) : tree.scheduledAttempts E ≤ 2 * (E + 1) := by
  unfold scheduledAttempts rejectionScheduleAttempts
  exact Nat.mul_le_mul_right (E + 1) (tree.factorCeiling_small_error hc hs)

end RationalWeightedGuideTree
end Blotto
