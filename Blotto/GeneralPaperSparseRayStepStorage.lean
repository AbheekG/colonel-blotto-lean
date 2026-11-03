import Blotto.GeneralPaperSourceEndpointCallerRates

/-! Actual native sparse accumulator step: both incoming/outgoing sums,
coefficient, coordinate operands, products, primitive scratch and encoded
native partial-work fields. Original lattices bound each reduced operand. -/
namespace Blotto.GeneralPaperSparseRayStepStorage
open RationalOrderCell GeneralPaperRayRationalBound GeneralPaperRationalPrimitivePrice
open GeneralPaperEncodedScalarStorage GeneralPaperRaySparseEvaluation
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem point_height {D E U Z R M : ℕ} {q : ℚ} (hD : 0<D)
    (hR : GeneralPaperRayAffineBound.rootWidth D E U Z≤R) (hq : Bounded D M q) (hM : M≤U) : RationalHeight q R := by
  apply ((hq.mono hM).height hD).mono
  unfold GeneralPaperRayAffineBound.rootWidth at hR
  omega

theorem velocity_height {D E U Z R M : ℕ} {q : ℚ} (hE : 0<E)
    (hR : GeneralPaperRayAffineBound.rootWidth D E U Z≤R) (hq : Bounded E M q) (hM : M≤Z) : RationalHeight q R := by
  apply ((hq.mono hM).height hE).mono
  unfold GeneralPaperRayAffineBound.rootWidth at hR
  omega

def cap (model : RationalCostModel) (W R : ℕ) : ℕ := 1+48*W+9*model.rat (1+2*R)

def window {v : Type*} (model : RationalCostModel) (W : ℕ) (x w : v → ℚ) (term : v×ℤ) (a b : ℚ) : ℕ :=
  let c := (term.2:ℚ)
  let px := c*x term.1
  let pv := c*w term.1
  let result := GeneralPaperSparseRayPrice.step model.rat W x w term a b
  let literal := model.rat (rationalWordWidth c)
  let multX := binary model.rat (·*·) c (x term.1)
  let multV := binary model.rat (·*·) c (w term.1)
  let addX := binary model.rat (·+·) a px
  let addV := binary model.rat (·+·) b pv
  rationalWordWidth c+rationalWordWidth (x term.1)+rationalWordWidth (w term.1)+rationalWordWidth a+rationalWordWidth b+
    rationalWordWidth px+rationalWordWidth pv+rationalWordWidth result.point+rationalWordWidth result.velocity+
    literal+multX+multV+addX+addV+
    fields W [48*W,literal,multX,multV,addX,addV,48*W+literal,48*W+literal+multX,
      48*W+literal+multX+multV,48*W+literal+multX+multV+addX,result.work]+256*W

def profile (model : RationalCostModel) (W R : ℕ) : ℕ :=
  9*(1+2*R)+9*model.rat (1+2*R)+11*(natBits (cap model W R)+W)+288*W

theorem bounded {v : Type*} (model : RationalCostModel) (W D E X V U Z R A B : ℕ)
    (hD : 0<D) (hE : 0<E) (hU : 1≤U) (hX : X≤U) (hV : V≤Z)
    (hR : GeneralPaperRayAffineBound.rootWidth D E U Z≤R) (x w : v → ℚ)
    (hx : ∀ j,Bounded D X (x j)) (hw : ∀ j,Bounded E V (w j)) (term : v×ℤ) (hc : term.2.natAbs≤1)
    (a b : ℚ) (ha : Bounded D A a) (hb : Bounded E B b) (hA : A+X≤U) (hB : B+V≤Z) :
    window model W x w term a b≤profile model W R := by
  let c := (term.2:ℚ)
  let px := c*x term.1
  let pv := c*w term.1
  let result := GeneralPaperSparseRayPrice.step model.rat W x w term a b
  let literal := model.rat (rationalWordWidth c)
  let multX := binary model.rat (·*·) c (x term.1)
  let multV := binary model.rat (·*·) c (w term.1)
  let addX := binary model.rat (·+·) a px
  let addV := binary model.rat (·+·) b pv
  have hC := point_height hD hR (Bounded.intCast D term.2) (hc.trans hU)
  have hXX := point_height hD hR (hx term.1) hX
  have hVV := velocity_height hE hR (hw term.1) hV
  have hAA := point_height hD hR ha (by omega)
  have hBB := velocity_height hE hR hb (by omega)
  have hPX := GeneralPaperRaySparseSize.term D X x hx term hc
  have hPV := GeneralPaperRaySparseSize.term E V w hw term hc
  have hPXH := point_height hD hR hPX hX
  have hPVH := velocity_height hE hR hPV hV
  have hNX := point_height hD hR (ha.add hPX) hA
  have hNV := velocity_height hE hR (hb.add hPV) hB
  have hLiteral : literal≤model.rat (1+2*R) := model.monotone (rationalWordWidth_of_height hC)
  have hMX : multX≤2*model.rat (1+2*R) := binary_le model.rat model.monotone (·*·) _ _ _
    (rationalWordWidth_of_height hC) (rationalWordWidth_of_height hXX) (rationalWordWidth_of_height hPXH)
  have hMV : multV≤2*model.rat (1+2*R) := binary_le model.rat model.monotone (·*·) _ _ _
    (rationalWordWidth_of_height hC) (rationalWordWidth_of_height hVV) (rationalWordWidth_of_height hPVH)
  have hAX : addX≤2*model.rat (1+2*R) := binary_le model.rat model.monotone (·+·) _ _ _
    (rationalWordWidth_of_height hAA) (rationalWordWidth_of_height hPXH) (rationalWordWidth_of_height hNX)
  have hAV : addV≤2*model.rat (1+2*R) := binary_le model.rat model.monotone (·+·) _ _ _
    (rationalWordWidth_of_height hBB) (rationalWordWidth_of_height hPVH) (rationalWordWidth_of_height hNV)
  have hShape : result.work=48*W+literal+multX+multV+addX+addV := rfl
  have hFields := fields_bound W (natBits (cap model W R))
    [48*W,literal,multX,multV,addX,addV,48*W+literal,48*W+literal+multX,
      48*W+literal+multX+multV,48*W+literal+multX+multV+addX,result.work] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold cap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤11*(natBits (cap model W R)+W)+32*W at hFields
  have h1 := rationalWordWidth_of_height hC
  have h2 := rationalWordWidth_of_height hXX
  have h3 := rationalWordWidth_of_height hVV
  have h4 := rationalWordWidth_of_height hAA
  have h5 := rationalWordWidth_of_height hBB
  have h6 := rationalWordWidth_of_height hPXH
  have h7 := rationalWordWidth_of_height hPVH
  have h8 : rationalWordWidth result.point≤1+2*R := rationalWordWidth_of_height hNX
  have h9 : rationalWordWidth result.velocity≤1+2*R := rationalWordWidth_of_height hNV
  change rationalWordWidth c+rationalWordWidth (x term.1)+rationalWordWidth (w term.1)+rationalWordWidth a+rationalWordWidth b+
    rationalWordWidth px+rationalWordWidth pv+rationalWordWidth result.point+rationalWordWidth result.velocity+
    literal+multX+multV+addX+addV+GeneralPaperEncodedScalarStorage.fields W
      [48*W,literal,multX,multV,addX,addV,48*W+literal,48*W+literal+multX,
        48*W+literal+multX+multV,48*W+literal+multX+multV+addX,result.work]+256*W≤_
  change rationalWordWidth c≤1+2*R at h1
  change rationalWordWidth px≤1+2*R at h6
  change rationalWordWidth pv≤1+2*R at h7
  unfold profile
  omega

end Blotto.GeneralPaperSparseRayStepStorage
