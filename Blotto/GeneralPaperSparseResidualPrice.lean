import Blotto.GeneralPaperSparseRayPrice

/-! Complete native sparse residual construction, including the final RHS
constant conversion/subtraction and affine result. The point/velocity sums
are the original sparse pass; coefficient aggregation remains proof-only.
-/
namespace Blotto.GeneralPaperSparseResidualPrice
open GeneralPaperAffineConstraintRows GeneralPaperRayRationalBound GeneralPaperRayAffine GeneralPaperRationalPrimitivePrice
set_option autoImplicit false
set_option maxHeartbeats 4500000

def evaluate {v : Type*} (primitive : ℕ → ℕ) (W : ℕ) (r : Row v) (x w : v → ℚ) : Affine × ℕ :=
  let sums := GeneralPaperSparseRayPrice.loop primitive W x w r.terms 0 0 0
  (⟨sums.point-(r.constant:ℚ),sums.velocity⟩,
    sums.work+24*W+primitive (rationalWordWidth (r.constant:ℚ))+binary primitive (·-·) sums.point (r.constant:ℚ))

theorem data {v : Type*} (primitive : ℕ → ℕ) (W : ℕ) (r : Row v) (x w : v → ℚ) :
    (evaluate primitive W r x w).1=(GeneralPaperRaySparseEvaluation.evaluate r x w).1 := by
  have hn := GeneralPaperSparseRayPrice.loop_data primitive W x w r.terms 0 0 0
  have ho := GeneralPaperRaySparseEvaluation.evaluate_data r x w
  have ha : (GeneralPaperSparseRayPrice.loop primitive W x w r.terms 0 0 0).point-(r.constant:ℚ)=
      (GeneralPaperRaySparseEvaluation.evaluate r x w).1.intercept := by rw [hn.1,ho.1,zero_add]
  have hb : (GeneralPaperSparseRayPrice.loop primitive W x w r.terms 0 0 0).velocity=
      (GeneralPaperRaySparseEvaluation.evaluate r x w).1.slope := by rw [hn.2,ho.2,zero_add]
  change Affine.mk ((GeneralPaperSparseRayPrice.loop primitive W x w r.terms 0 0 0).point-(r.constant:ℚ))
    (GeneralPaperSparseRayPrice.loop primitive W x w r.terms 0 0 0).velocity=_
  rw [ha,hb]

theorem work {v : Type*} (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W D E X V U Z R : ℕ) (hD : 0<D) (hE : 0<E) (hU : 1≤U) (hX : X≤U) (hV : V≤Z)
    (hR : GeneralPaperRayAffineBound.rootWidth D E U Z≤R) (r : Row v) (x w : v → ℚ)
    (hx : ∀ j,Bounded D X (x j)) (hw : ∀ j,Bounded E V (w j))
    (hc : ∀ t∈r.terms,t.2.natAbs≤1) (hConst : r.constant.natAbs≤1)
    (hMassX : r.terms.length*X+1≤U) (hMassV : r.terms.length*V≤Z) :
    (evaluate primitive W r x w).2≤r.terms.length*(48*W+9*primitive (1+2*R))+26*W+3*primitive (1+2*R) := by
  let sums := GeneralPaperSparseRayPrice.loop primitive W x w r.terms 0 0 0
  have hLoop := GeneralPaperSparseRayPrice.loop_work primitive hMono W D E X V U Z R hD hE hU hX hV hR
    x w hx hw r.terms hc 0 0 0 0 0 (Bounded.zero D) (Bounded.zero E)
    (by simp only [Nat.zero_add]; omega) (by simpa only [Nat.zero_add] using hMassV)
  have hn := GeneralPaperSparseRayPrice.loop_data primitive W x w r.terms 0 0 0
  have hPoint : Bounded D (r.terms.length*X) sums.point := by
    change Bounded D (r.terms.length*X) (GeneralPaperSparseRayPrice.loop primitive W x w r.terms 0 0 0).point
    rw [hn.1,zero_add]
    exact Bounded.list_sum D X _ r.terms (fun t ht => GeneralPaperRaySparseSize.term D X x hx t (hc t ht))
  have hC := (Bounded.intCast D r.constant).mono hConst
  have hResult := hPoint.sub hC
  have hWord (q : ℚ) {M : ℕ} (hq : Bounded D M q) (hM : M≤U) : rationalWordWidth q≤1+2*R := by
    apply rationalWordWidth_of_height
    apply ((hq.mono hM).height hD).mono
    unfold GeneralPaperRayAffineBound.rootWidth at hR
    omega
  have hCast := hMono (hWord _ hC hU)
  have hSubtract := binary_le primitive hMono (·-·) sums.point (r.constant:ℚ) (1+2*R)
    (hWord _ hPoint (by omega)) (hWord _ hC hU) (hWord _ hResult hMassX)
  change sums.work+24*W+primitive (rationalWordWidth (r.constant:ℚ))+binary primitive (·-·) sums.point (r.constant:ℚ)≤_
  change sums.work≤_ at hLoop
  simp only [Nat.zero_add] at hLoop
  nlinarith only [hLoop,hCast,hSubtract]

end Blotto.GeneralPaperSparseResidualPrice
