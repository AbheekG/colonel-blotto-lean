import Blotto.GeneralPaperPhysicalPhaseCapacity

/-! The paper's two positive normalized value roundings. Ceiling is a
mathematical comparator here; native independent coordinate implementations
are joined separately. Equal entries remain equal and all errors are L1. -/
namespace Blotto.GeneralPaperPositiveValueRounding
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

theorem input_le_one {n : ℕ} (v : RationalFieldSelector n) (j : Fin n) : v.weight j≤1 := by
  have h := Finset.single_le_sum (s:=Finset.univ) (f:=v.weight) (fun i _ => (v.positive i).le) (Finset.mem_univ j)
  simpa only [v.sum_one] using h

def weight {n : ℕ} (M : ℕ) (v : RationalFieldSelector n) (j : Fin n) : ℕ := ⌈(M:ℚ)*v.weight j⌉₊
def total {n : ℕ} (M : ℕ) (v : RationalFieldSelector n) : ℕ := ∑ j,weight M v j

theorem positive_weight {n : ℕ} (M : ℕ) (hM : 0<M) (v : RationalFieldSelector n) (j : Fin n) : 0<weight M v j :=
  Nat.ceil_pos.mpr (mul_pos (by exact_mod_cast hM) (v.positive j))

theorem error_nonnegative {n : ℕ} (M : ℕ) (v : RationalFieldSelector n) (j : Fin n) :
    0≤(weight M v j:ℚ)-(M:ℚ)*v.weight j := sub_nonneg.mpr (Nat.le_ceil _)

theorem error_lt_one {n : ℕ} (M : ℕ) (v : RationalFieldSelector n) (j : Fin n) :
    (weight M v j:ℚ)-(M:ℚ)*v.weight j<1 := by
  have h := Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg M) (v.positive j).le)
  change (⌈(M:ℚ)*v.weight j⌉₊:ℚ)-(M:ℚ)*v.weight j<1
  linarith only [h]

theorem total_cast {n : ℕ} (M : ℕ) (v : RationalFieldSelector n) : (total M v:ℚ)=∑ j,(weight M v j:ℚ) := by
  unfold total
  push_cast
  rfl

theorem total_error {n : ℕ} (M : ℕ) (v : RationalFieldSelector n) :
    (total M v:ℚ)-M=∑ j,((weight M v j:ℚ)-(M:ℚ)*v.weight j) := by
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,v.sum_one,mul_one,total_cast]

theorem total_lower {n : ℕ} (M : ℕ) (v : RationalFieldSelector n) : M≤total M v := by
  have h := Finset.sum_nonneg (s:=Finset.univ) (fun j _ => error_nonnegative M v j)
  rw [←total_error] at h
  exact_mod_cast (show (M:ℚ)≤total M v by linarith only [h])

theorem total_upper {n : ℕ} (M : ℕ) (v : RationalFieldSelector n) : total M v<M+n := by
  have hn := v.fields_positive
  have h : (∑ j,((weight M v j:ℚ)-(M:ℚ)*v.weight j))<(n:ℚ) := by
    have hh := Finset.sum_lt_sum_of_nonempty
      (show (Finset.univ : Finset (Fin n)).Nonempty from ⟨⟨0,hn⟩,Finset.mem_univ _⟩)
      (fun j _ => error_lt_one M v j)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using hh
  rw [←total_error] at h
  exact_mod_cast (show (total M v:ℚ)<M+n by linarith only [h])

theorem total_positive {n : ℕ} (M : ℕ) (hM : 0<M) (v : RationalFieldSelector n) : 0<total M v :=
  hM.trans_le (total_lower M v)

def normalized {n : ℕ} (M : ℕ) (hM : 0<M) (v : RationalFieldSelector n) : RationalFieldSelector n where
  weight := fun j => (weight M v j:ℚ)/total M v
  positive := fun j => div_pos (by exact_mod_cast positive_weight M hM v j) (by exact_mod_cast total_positive M hM v)
  sum_one := by
    rw [←Finset.sum_div,←total_cast,div_self (by exact_mod_cast (total_positive M hM v).ne')]

theorem equal_weights {n : ℕ} (M : ℕ) (v : RationalFieldSelector n) (i j : Fin n) (h : v.weight i=v.weight j) :
    weight M v i=weight M v j := by unfold weight; rw [h]

theorem equal_normalized {n : ℕ} (M : ℕ) (hM : 0<M) (v : RationalFieldSelector n) (i j : Fin n)
    (h : v.weight i=v.weight j) : (normalized M hM v).weight i=(normalized M hM v).weight j := by
  dsimp only [normalized]
  rw [equal_weights M v i j h]

theorem weight_le_total {n : ℕ} (M : ℕ) (v : RationalFieldSelector n) (j : Fin n) : weight M v j≤total M v :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

theorem point_error {n : ℕ} (M : ℕ) (hM : 0<M) (v : RationalFieldSelector n) (j : Fin n) :
    |(normalized M hM v).weight j-v.weight j|≤
      ((weight M v j:ℚ)-(M:ℚ)*v.weight j)/(total M v:ℚ)+v.weight j*((total M v:ℚ)-M)/(total M v:ℚ) := by
  have hQ : (0:ℚ)<total M v := by exact_mod_cast total_positive M hM v
  have hD : (0:ℚ)≤(total M v:ℚ)-M := sub_nonneg.mpr (by exact_mod_cast total_lower M v)
  have he : (normalized M hM v).weight j-v.weight j=
      ((weight M v j:ℚ)-(M:ℚ)*v.weight j)/(total M v:ℚ)-v.weight j*((total M v:ℚ)-M)/(total M v:ℚ) := by
    dsimp only [normalized]
    field_simp
    ring
  rw [he]
  have ha := div_nonneg (error_nonnegative M v j) hQ.le
  have hb := div_nonneg (mul_nonneg (v.positive j).le hD) hQ.le
  simpa only [abs_of_nonneg ha,abs_of_nonneg hb] using abs_sub
    (((weight M v j:ℚ)-(M:ℚ)*v.weight j)/(total M v:ℚ)) (v.weight j*((total M v:ℚ)-M)/(total M v:ℚ))

theorem l1_error {n : ℕ} (M : ℕ) (hM : 0<M) (v : RationalFieldSelector n) :
    (∑ j,|(normalized M hM v).weight j-v.weight j|)≤2*(n:ℚ)/(M:ℚ) := by
  have hQ : (0:ℚ)<total M v := by exact_mod_cast total_positive M hM v
  have hM' : (0:ℚ)<M := by exact_mod_cast hM
  have hQM : (M:ℚ)≤total M v := by exact_mod_cast total_lower M v
  have hGap : (total M v:ℚ)-M≤n := by
    have h := total_upper M v
    have hh : (total M v:ℚ)<M+n := by exact_mod_cast h
    linarith only [hh]
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => point_error M hM v j)
  have he : (∑ j,(((weight M v j:ℚ)-(M:ℚ)*v.weight j)/(total M v:ℚ)+v.weight j*((total M v:ℚ)-M)/(total M v:ℚ)))=
      2*((total M v:ℚ)-M)/(total M v:ℚ) := by
    rw [Finset.sum_add_distrib,←Finset.sum_div,←total_error,←Finset.sum_div,←Finset.sum_mul,v.sum_one]
    ring
  rw [he] at hs
  exact hs.trans ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hGap (by norm_num)) hQ.le).trans
    (div_le_div_of_nonneg_left (by positivity) hM' hQM))

end Blotto.GeneralPaperPositiveValueRounding
