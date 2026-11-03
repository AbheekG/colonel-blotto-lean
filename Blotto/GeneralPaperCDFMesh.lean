import Blotto.GeneralPaperEpochLaw

/-! Actual downward rounding of a probability from its exact summed integer
numerator and denominator. The bounded quotient uses only arithmetic and
comparisons, with depth constructed from the selected dyadic mesh. The sums
are explicit inputs from the epoch arrays; this routine does not silently
recompute them by scanning the full code alphabet.
-/
namespace Blotto.GeneralPaperCDFMesh
open GeneralPaperBoundedQuotient GeneralPaperRoundedLosses
set_option autoImplicit false

def evaluate (numerator total mesh depth : ℕ) : GeneralPaperBoundedQuotient.Result :=
  let result := GeneralPaperBoundedQuotient.run ((mesh:ℚ)*numerator) total depth
  ⟨result.quotient,result.remainder,result.work+16⟩

theorem evaluate_spec (numerator total mesh depth : ℕ) (hTotal : 0<total)
    (hNumerator : numerator≤total) (hMesh : mesh<2^depth) :
    ((mesh:ℚ)*numerator)=(total:ℚ)*(evaluate numerator total mesh depth).quotient+
      (evaluate numerator total mesh depth).remainder ∧
    0≤(evaluate numerator total mesh depth).remainder ∧
      (evaluate numerator total mesh depth).remainder<total := by
  have ht : (0:ℚ)<total := by exact_mod_cast hTotal
  have hn : (numerator:ℚ)≤total := by exact_mod_cast hNumerator
  have hm : (mesh:ℚ)<(2:ℚ)^depth := by exact_mod_cast hMesh
  apply GeneralPaperBoundedQuotient.run_spec _ _ ht depth (by positivity)
  have h1 := mul_le_mul_of_nonneg_left hn (show (0:ℚ)≤mesh by positivity)
  have h2 := mul_lt_mul_of_pos_left hm ht
  nlinarith

theorem evaluate_floor (numerator total mesh depth : ℕ) (hTotal : 0<total)
    (hNumerator : numerator≤total) (hMesh : mesh<2^depth) :
    (evaluate numerator total mesh depth).quotient=⌊(mesh:ℚ)*numerator/total⌋₊ := by
  have hs := evaluate_spec numerator total mesh depth hTotal hNumerator hMesh
  have ht : (0:ℚ)<total := by exact_mod_cast hTotal
  have hlo : ((evaluate numerator total mesh depth).quotient:ℚ)≤(mesh:ℚ)*numerator/total := by
    apply (le_div_iff₀ ht).mpr
    nlinarith only [hs.1,hs.2.1]
  have hhi : (mesh:ℚ)*numerator/total<((evaluate numerator total mesh depth).quotient:ℚ)+1 := by
    apply (div_lt_iff₀ ht).mpr
    nlinarith only [hs.1,hs.2.2]
  symm
  exact (Nat.floor_eq_iff (by positivity)).mpr ⟨hlo,hhi⟩

theorem evaluate_bound (numerator total mesh depth : ℕ) (hTotal : 0<total)
    (hNumerator : numerator≤total) (hMesh : mesh<2^depth) :
    (evaluate numerator total mesh depth).quotient≤mesh := by
  have hs := evaluate_spec numerator total mesh depth hTotal hNumerator hMesh
  have ht : (0:ℚ)<total := by exact_mod_cast hTotal
  have hn : (numerator:ℚ)≤total := by exact_mod_cast hNumerator
  have hm : (0:ℚ)≤mesh := by positivity
  have hh := mul_le_mul_of_nonneg_left hn hm
  have hq : ((evaluate numerator total mesh depth).quotient:ℚ)≤mesh := by nlinarith only [hs.1,hs.2.1,ht,hh]
  exact_mod_cast hq

theorem evaluate_zero (total mesh depth : ℕ) (hTotal : 0<total) (hMesh : mesh<2^depth) :
    (evaluate 0 total mesh depth).quotient=0 := by
  rw [evaluate_floor 0 total mesh depth hTotal (by omega) hMesh]
  norm_num

theorem evaluate_one (total mesh depth : ℕ) (hTotal : 0<total) (hMesh : mesh<2^depth) :
    (evaluate total total mesh depth).quotient=mesh := by
  rw [evaluate_floor total total mesh depth hTotal (by omega) hMesh]
  have ht : (total:ℚ)≠0 := by exact_mod_cast ne_of_gt hTotal
  rw [mul_div_cancel_right₀ _ ht,Nat.floor_natCast]

theorem evaluate_monotone (small large total mesh depth : ℕ) (hTotal : 0<total)
    (hLarge : large≤total) (hOrder : small≤large) (hMesh : mesh<2^depth) :
    (evaluate small total mesh depth).quotient≤(evaluate large total mesh depth).quotient := by
  rw [evaluate_floor small total mesh depth hTotal (by omega) hMesh,
    evaluate_floor large total mesh depth hTotal hLarge hMesh]
  apply Nat.floor_mono
  have he : (small:ℚ)≤large := by exact_mod_cast hOrder
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity)) (by positivity)

theorem evaluate_error (numerator total mesh depth : ℕ) (hTotal : 0<total) (hM : 0<mesh)
    (hNumerator : numerator≤total) (hMesh : mesh<2^depth) :
    0≤(numerator:ℚ)/total-component mesh (evaluate numerator total mesh depth).quotient ∧
      (numerator:ℚ)/total-component mesh (evaluate numerator total mesh depth).quotient<1/(mesh:ℚ) := by
  have hs := evaluate_spec numerator total mesh depth hTotal hNumerator hMesh
  have ht : (0:ℚ)<total := by exact_mod_cast hTotal
  have hm : (0:ℚ)<mesh := by exact_mod_cast hM
  have he : (numerator:ℚ)/total-component mesh (evaluate numerator total mesh depth).quotient=
      (evaluate numerator total mesh depth).remainder/((mesh:ℚ)*total) := by
    unfold component
    apply (eq_div_iff (ne_of_gt (mul_pos hm ht))).mpr
    field_simp
    nlinarith only [hs.1]
  rw [he]
  refine ⟨div_nonneg hs.2.1 (mul_pos hm ht).le,?_⟩
  apply (div_lt_iff₀ (mul_pos hm ht)).mpr
  have hEq : (1/(mesh:ℚ))*((mesh:ℚ)*total)=(total:ℚ) := by field_simp
  rw [hEq]
  exact hs.2.2

theorem evaluate_work (numerator total mesh depth : ℕ) :
    (evaluate numerator total mesh depth).work=12*depth+18 := by
  unfold evaluate
  dsimp only
  rw [GeneralPaperBoundedQuotient.run_work]

def selected (k numerator total : ℕ) : GeneralPaperBoundedQuotient.Result :=
  evaluate numerator total (GeneralPaperSourceParameters.prepare k).meshDenominator (30+k)

theorem selected_depth (k : ℕ) : (GeneralPaperSourceParameters.prepare k).meshDenominator<2^(30+k) := by
  rw [(GeneralPaperSourceParameters.data k).2.2.2.2.1]
  have he := GeneralPaperBoundedQuotient.dyadic_cap (29+k)
  convert he using 1 <;> congr 1 <;> omega

theorem selected_bounds (k numerator total : ℕ) (hTotal : 0<total) (hNumerator : numerator≤total) :
    (selected k numerator total).quotient≤(GeneralPaperSourceParameters.prepare k).meshDenominator ∧
    |(numerator:ℚ)/total-component (GeneralPaperSourceParameters.prepare k).meshDenominator
      (selected k numerator total).quotient|≤(GeneralPaperSourceParameters.prepare k).theta := by
  have hm := GeneralPaperSourceParameters.mesh_positive k
  have he := evaluate_error numerator total _ _ hTotal hm hNumerator (selected_depth k)
  refine ⟨evaluate_bound numerator total _ _ hTotal hNumerator (selected_depth k),?_⟩
  unfold selected
  rw [abs_of_nonneg he.1,GeneralPaperSourceParameters.theta_mesh]
  exact he.2.le

theorem selected_work (k numerator total : ℕ) : (selected k numerator total).work=12*(30+k)+18 :=
  evaluate_work _ _ _ _

theorem selected_component_bounds (k numerator total : ℕ) (hTotal : 0<total) (hNumerator : numerator≤total) :
    0≤component (GeneralPaperSourceParameters.prepare k).meshDenominator (selected k numerator total).quotient ∧
      component (GeneralPaperSourceParameters.prepare k).meshDenominator (selected k numerator total).quotient≤1 :=
  component_bounds _ _ (GeneralPaperSourceParameters.mesh_positive k) (selected_bounds k numerator total hTotal hNumerator).1

theorem selected_real_error (k numerator total : ℕ) (hTotal : 0<total) (hNumerator : numerator≤total) :
    |(numerator:ℝ)/total-(component (GeneralPaperSourceParameters.prepare k).meshDenominator
      (selected k numerator total).quotient:ℝ)|≤(GeneralPaperSourceParameters.prepare k).theta := by
  have h := (selected_bounds k numerator total hTotal hNumerator).2
  have hc : ((|(numerator:ℚ)/total-component (GeneralPaperSourceParameters.prepare k).meshDenominator
      (selected k numerator total).quotient|:ℚ):ℝ)≤((GeneralPaperSourceParameters.prepare k).theta:ℝ) := by
    exact_mod_cast h
  push_cast at hc
  exact hc

theorem selected_true_error (k numerator total : ℕ) (hTotal : 0<total) (hNumerator : numerator≤total)
    (trueProbability queryError : ℝ) (hQuery : |trueProbability-(numerator:ℝ)/total|≤queryError) :
    |trueProbability-(component (GeneralPaperSourceParameters.prepare k).meshDenominator
      (selected k numerator total).quotient:ℝ)|≤queryError+(GeneralPaperSourceParameters.prepare k).theta := by
  have hm := selected_real_error k numerator total hTotal hNumerator
  have he := abs_add_le (trueProbability-(numerator:ℝ)/total)
    ((numerator:ℝ)/total-(component (GeneralPaperSourceParameters.prepare k).meshDenominator
      (selected k numerator total).quotient:ℝ))
  have hEq : trueProbability-(numerator:ℝ)/total+
    ((numerator:ℝ)/total-(component (GeneralPaperSourceParameters.prepare k).meshDenominator
      (selected k numerator total).quotient:ℝ))=trueProbability-
        (component (GeneralPaperSourceParameters.prepare k).meshDenominator (selected k numerator total).quotient:ℝ) := by ring
  rw [hEq] at he
  linarith

end Blotto.GeneralPaperCDFMesh
