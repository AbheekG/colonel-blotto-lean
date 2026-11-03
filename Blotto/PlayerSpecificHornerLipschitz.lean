import Blotto.PlayerSpecificFieldCallerContracts

/-! Explicit Horner continuity bound for exact sign refinement. It uses
only coefficient magnitudes and a finite interval enclosure. -/
namespace Blotto.PlayerSpecificHornerLipschitz
open PlayerSpecificDensePolynomial PlayerSpecificSturmVariations
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem step_profile (n : ℕ) (M T : ℝ) (hM : 0≤M) (hT : 0≤T) :
    T+M*((n:ℝ)*T)≤((n:ℝ)+1)*T*(1+M) := by
  have hn : (0:ℝ)≤n := Nat.cast_nonneg n
  have hh : 1+M*(n:ℝ)≤((n:ℝ)+1)*(1+M) := by nlinarith only [hM,hn]
  have hm:=mul_le_mul_of_nonneg_left hh hT
  nlinarith only [hm]

theorem bound (a : Data) (U M x y : ℝ) (hU : 0≤U) (hM : 0≤M)
    (hx : |x| ≤ M) (hy : |y| ≤ M) (h : ∀ q∈a,|(q:ℝ)| ≤ U) :
    |realEvaluate a x-realEvaluate a y| ≤ (a.length:ℝ)*U*(1+M)^a.length*|x-y| := by
  induction a with
  | nil => simp only [realEvaluate,List.foldr_nil,List.length_nil,Nat.cast_zero,pow_zero,zero_mul,sub_self,abs_zero,le_refl]
  | cons c cs ih =>
    have htail : ∀ q∈cs,|(q:ℝ)| ≤ U := fun q hq => h q (List.mem_cons_of_mem c hq)
    have hp:=PlayerSpecificEvaluationMagnitude.horner_bound cs U M x hU hM hx htail
    have hd:=ih htail
    have hT : 0≤U*(1+M)^cs.length*|x-y| :=
      mul_nonneg (mul_nonneg hU (pow_nonneg (by linarith) _)) (abs_nonneg _)
    have hs:=step_profile cs.length M (U*(1+M)^cs.length*|x-y|) hM hT
    calc
      _ = |(x-y)*realEvaluate cs x+y*(realEvaluate cs x-realEvaluate cs y)| := by
        congr 1
        simp only [realEvaluate,List.foldr_cons]
        ring
      _ ≤ |x-y| * |realEvaluate cs x| + |y| * |realEvaluate cs x-realEvaluate cs y| := by
        simpa only [abs_mul] using abs_add_le ((x-y)*realEvaluate cs x) (y*(realEvaluate cs x-realEvaluate cs y))
      _ ≤ |x-y| * (U*(1+M)^cs.length)+M*((cs.length:ℝ)*U*(1+M)^cs.length*|x-y|) :=
        add_le_add (mul_le_mul_of_nonneg_left hp (abs_nonneg _))
          (mul_le_mul hy hd (abs_nonneg _) hM)
      _ ≤ _ := by
        rw [List.length_cons,Nat.cast_add,Nat.cast_one,pow_succ]
        nlinarith only [hs]

theorem encoded (a : Data) (M x y : ℝ) (hM : 0≤M) (hx : |x| ≤ M) (hy : |y| ≤ M) :
    |realEvaluate a x-realEvaluate a y| ≤
      (a.length:ℝ)*(2:ℝ)^PlayerSpecificRationalMagnitude.inputHeight a*(1+M)^a.length*|x-y| := by
  apply bound a _ M x y (pow_nonneg (by norm_num) _) hM hx hy
  intro q hq
  exact (PlayerSpecificRationalMagnitude.real_upper q _ (PlayerSpecificRationalMagnitude.member_height a q hq)).le

end Blotto.PlayerSpecificHornerLipschitz
