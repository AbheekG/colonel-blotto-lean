import Blotto.GeneralPaperLowerQuantile

/-! Exact uniform lower-quantile rank counts and both probability bounds.
All divisions/counts are erased proof analysis of comparison deviations. -/
namespace Blotto.GeneralPaperQuantileRankCount
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 900000

theorem prefix_card (N A : ℕ) : (Finset.univ.filter (fun i:Fin N => i.val<A)).card=min N A := by
  by_cases h : A<N
  · have he : Finset.univ.filter (fun i:Fin N => i.val<A)=Finset.Iio (⟨A,h⟩:Fin N) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iio]
      rfl
    rw [he,Fin.card_Iio,Nat.min_eq_right h.le]
  · have hNA : N≤A := Nat.le_of_not_gt h
    have he : Finset.univ.filter (fun i:Fin N => i.val<A)=Finset.univ :=
      Finset.filter_true_of_mem (fun i _ => i.isLt.trans_le hNA)
    rw [he,Finset.card_univ,Fintype.card_fin,Nat.min_eq_left hNA]

noncomputable def count (R W f : ℕ) : ℕ := (Finset.univ.filter (fun a:Fin R => a.val*W≤R*f)).card

theorem formula (R W f : ℕ) (hW : 0<W) : count R W f=min R ((R*f)/W+1) := by
  have he : Finset.univ.filter (fun a:Fin R => a.val*W≤R*f)=
      Finset.univ.filter (fun a:Fin R => a.val<(R*f)/W+1) := by
    ext a
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [←Nat.le_div_iff_mul_le hW]
    omega
  unfold count
  rw [he,prefix_card]

theorem integer_bounds (R W f : ℕ) (hW : 0<W) (hf : f≤W) :
    R*f≤count R W f*W ∧ count R W f*W≤R*f+W := by
  rw [formula R W f hW]
  let q := (R*f)/W
  have hRec := Nat.mod_add_div (R*f) W
  change (R*f)%W+W*q=R*f at hRec
  have hRem := Nat.mod_lt (R*f) hW
  have hNonneg : 0≤(R*f)%W := Nat.zero_le _
  change R*f≤min R (q+1)*W ∧ min R (q+1)*W≤R*f+W
  by_cases h : R≤q+1
  · rw [Nat.min_eq_left h]
    have hMul := Nat.mul_le_mul_right W h
    exact ⟨Nat.mul_le_mul_left R hf,by nlinarith only [hMul,hRec,hNonneg]⟩
  · rw [Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))]
    constructor <;> nlinarith only [hRec,hRem,hNonneg]

theorem probability_bounds (R W f : ℕ) (hR : 0<R) (hW : 0<W) (hf : f≤W) :
    0≤(count R W f:ℝ)/R-(f:ℝ)/W ∧
      (count R W f:ℝ)/R-(f:ℝ)/W≤1/(R:ℝ) := by
  have h := integer_bounds R W f hW hf
  have h0 : (R:ℝ)*f≤(count R W f:ℝ)*W := by exact_mod_cast h.1
  have h1 : (count R W f:ℝ)*W≤(R:ℝ)*f+W := by exact_mod_cast h.2
  have hr : (R:ℝ)≠0 := by exact_mod_cast hR.ne'
  have hw : (W:ℝ)≠0 := by exact_mod_cast hW.ne'
  have hd : (0:ℝ)<(R*W:ℕ) := by exact_mod_cast Nat.mul_pos hR hW
  have he : ((count R W f:ℝ)/R-(f:ℝ)/W)*(R*W:ℕ)=(count R W f:ℝ)*W-(R:ℝ)*f := by
    push_cast
    field_simp
  have hOne : (1/(R:ℝ))*(R*W:ℕ)=(W:ℝ) := by push_cast; field_simp
  constructor
  · apply le_of_mul_le_mul_right (a:=((R*W:ℕ):ℝ)) ?_ hd
    rw [zero_mul,he]
    linarith only [h0]
  · apply le_of_mul_le_mul_right (a:=((R*W:ℕ):ℝ)) ?_ hd
    rw [he,hOne]
    linarith only [h1]

end Blotto.GeneralPaperQuantileRankCount
