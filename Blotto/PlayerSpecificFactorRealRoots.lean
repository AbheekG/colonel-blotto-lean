import Blotto.PlayerSpecificFactorContract

/-! Exact real-root transfer through the computed rational factorization.
No rationality decision is supplied: a failed reconstruction in the retained
isolating interval will exclude each of the removed rational roots. -/
namespace Blotto.PlayerSpecificFactorRealRoots
open PlayerSpecificDensePolynomial PlayerSpecificRationalFactors PlayerSpecificSturmVariations
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem product_nonzero (qs : Data) (x : ℝ) (hx : ∀ q ∈ qs,(q:ℝ)≠x) :
    (product qs).eval₂ (Rat.castHom ℝ) x≠0 := by
  induction qs with
  | nil => simp only [product,Polynomial.eval₂_one,ne_eq,one_ne_zero,not_false_eq_true]
  | cons q qs ih =>
    rw [product,Polynomial.eval₂_mul]
    apply mul_ne_zero
    · rw [PlayerSpecificLinearFactor.linear_semantics,Polynomial.eval₂_sub,Polynomial.eval₂_X,Polynomial.eval₂_C]
      exact sub_ne_zero.mpr (Ne.symm (hx q List.mem_cons_self))
    · exact ih (fun r hr => hx r (List.mem_cons_of_mem q hr))

theorem residual_root (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) (x : ℝ)
    (hroot : realEvaluate p x=0) (hexclude : ∀ q ∈ (factor p).1,(q:ℝ)≠x) :
    realEvaluate (factor p).2 x=0 := by
  have hc:=(factor_contract p hp hlen).2.2.2.1
  rw [←realEvaluate_semantics,hc,Polynomial.eval₂_mul] at hroot
  exact (realEvaluate_semantics _ x).symm.trans
    ((mul_eq_zero.mp hroot).resolve_left (product_nonzero _ x hexclude))

theorem original_root (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) (x : ℝ)
    (hroot : realEvaluate (factor p).2 x=0) : realEvaluate p x=0 := by
  rw [←realEvaluate_semantics,(factor_contract p hp hlen).2.2.2.1,Polynomial.eval₂_mul,
    realEvaluate_semantics,hroot,mul_zero]

theorem positive_degree (p : Data) (hp : semantics p≠0) (x : ℝ) (hroot : realEvaluate p x=0) :
    0<(semantics p).natDegree := by
  by_contra hz
  have hd : (semantics p).natDegree=0 := by omega
  have hc:=Polynomial.eq_C_of_natDegree_eq_zero hd
  rw [←realEvaluate_semantics,hc,Polynomial.eval₂_C] at hroot
  change (((semantics p).coeff 0:ℚ):ℝ)=0 at hroot
  have hzQ : (semantics p).coeff 0=0 := by exact_mod_cast hroot
  exact hp (by rw [hc,hzQ,map_zero])

end Blotto.PlayerSpecificFactorRealRoots
