import Blotto.GeneralPaperSparseRayLoopStorage

/-! Native zero-start sparse residual: complete accumulator traversal,
returned affine coefficients, final constant conversion/subtraction and
encoded sums/wrapper/partial-work counters. Row ownership is caller-owned. -/
namespace Blotto.GeneralPaperSparseResidualStorage
open RationalOrderCell GeneralPaperRayRationalBound GeneralPaperAffineConstraintRows
open GeneralPaperRationalPrimitivePrice GeneralPaperSparseRayStepStorage GeneralPaperEncodedScalarStorage
open GeneralPaperAffineWitnessStorage
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192

def price (model : RationalCostModel) (W N R : ℕ) : ℕ := N*(48*W+9*model.rat (1+2*R))+26*W+3*model.rat (1+2*R)
def metadataCap (model : RationalCostModel) (W N R : ℕ) : ℕ := N+1+3*price model W N R

def window {v : Type*} (model : RationalCostModel) (W : ℕ) (r : Row v) (x w : v → ℚ) : ℕ :=
  let sums := GeneralPaperSparseRayPrice.loop model.rat W x w r.terms 0 0 0
  let result := GeneralPaperSparseResidualPrice.evaluate model.rat W r x w
  let literal := model.rat (rationalWordWidth (r.constant:ℚ))
  let subtract := binary model.rat (·-·) sums.point (r.constant:ℚ)
  GeneralPaperSparseRayLoopStorage.frames model W x w r.terms 0 0 0+
    rationalWordWidth sums.point+rationalWordWidth sums.velocity+rationalWordWidth (r.constant:ℚ)+affineFoot W result.1+
    literal+subtract+fields W [r.terms.length,sums.work,literal,subtract,result.2,24*W,sums.work+24*W,sums.work+24*W+literal]+256*W

def profile (model : RationalCostModel) (W N R : ℕ) : ℕ :=
  (N+1)*GeneralPaperSparseRayLoopStorage.frameProfile model W R N (GeneralPaperSparseRayLoopStorage.zeroPrice model W R N)+
    3*(1+2*R)+affineProfile W R+3*model.rat (1+2*R)+8*(natBits (metadataCap model W N R)+W)+288*W

theorem bounded {v : Type*} (model : RationalCostModel) (W D E X V U Z R N : ℕ)
    (hD : 0<D) (hE : 0<E) (hU : 1≤U) (hX : X≤U) (hV : V≤Z)
    (hR : GeneralPaperRayAffineBound.rootWidth D E U Z≤R) (r : Row v) (x w : v → ℚ)
    (hx : ∀ j,Bounded D X (x j)) (hw : ∀ j,Bounded E V (w j)) (hLen : r.terms.length≤N)
    (hc : ∀ t∈r.terms,t.2.natAbs≤1) (hConst : r.constant.natAbs≤1)
    (hMassX : r.terms.length*X+1≤U) (hMassV : r.terms.length*V≤Z) :
    window model W r x w≤profile model W N R := by
  let sums := GeneralPaperSparseRayPrice.loop model.rat W x w r.terms 0 0 0
  let result := GeneralPaperSparseResidualPrice.evaluate model.rat W r x w
  let literal := model.rat (rationalWordWidth (r.constant:ℚ))
  let subtract := binary model.rat (·-·) sums.point (r.constant:ℚ)
  have hLoop := GeneralPaperSparseRayLoopStorage.zero_start model W D E X V U Z R N hD hE hU hX hV hR x w hx hw r.terms hLen hc (by omega) hMassV
  have hSums := GeneralPaperSparseRayLoopStorage.returned model W D E X V 0 0 x w hx hw r.terms hc 0 0 0 (Bounded.zero D) (Bounded.zero E)
  simp only [Nat.zero_add] at hSums
  have hPoint := point_height hD hR hSums.1 (by omega)
  have hVelocity := velocity_height hE hR hSums.2 hMassV
  have hConstant := (Bounded.intCast D r.constant).mono hConst
  have hCH := point_height hD hR hConstant hU
  have hResult := point_height hD hR (hSums.1.sub hConstant) hMassX
  have hAffine := affine_bound W R result.1 hResult hVelocity
  have hP : rationalWordWidth sums.point≤1+2*R := rationalWordWidth_of_height hPoint
  have hVW : rationalWordWidth sums.velocity≤1+2*R := rationalWordWidth_of_height hVelocity
  have hC := rationalWordWidth_of_height hCH
  have hLiteral : literal≤model.rat (1+2*R) := model.monotone hC
  have hSubtract : subtract≤2*model.rat (1+2*R) := binary_le model.rat model.monotone (·-·) _ _ _ hP hC (rationalWordWidth_of_height hResult)
  have hWork := (GeneralPaperSparseResidualPrice.work model.rat model.monotone W D E X V U Z R hD hE hU hX hV hR
    r x w hx hw hc hConst hMassX hMassV).trans (show
      r.terms.length*(48*W+9*model.rat (1+2*R))+26*W+3*model.rat (1+2*R)≤price model W N R by unfold price; gcongr)
  change result.2≤price model W N R at hWork
  have hShape : result.2=sums.work+24*W+literal+subtract := rfl
  have hFields := fields_bound W (natBits (metadataCap model W N R))
    [r.terms.length,sums.work,literal,subtract,result.2,24*W,sums.work+24*W,sums.work+24*W+literal] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤8*(natBits (metadataCap model W N R)+W)+32*W at hFields
  change GeneralPaperSparseRayLoopStorage.frames model W x w r.terms 0 0 0+
    rationalWordWidth sums.point+rationalWordWidth sums.velocity+rationalWordWidth (r.constant:ℚ)+affineFoot W result.1+
    literal+subtract+GeneralPaperEncodedScalarStorage.fields W
      [r.terms.length,sums.work,literal,subtract,result.2,24*W,sums.work+24*W,sums.work+24*W+literal]+256*W≤_
  unfold profile
  omega

end Blotto.GeneralPaperSparseResidualStorage
