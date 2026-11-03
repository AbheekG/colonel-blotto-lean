import Blotto.GeneralPaperSourceEndpointInputRates

/-! Actual two-operation affine evaluation: coefficients, sample, product,
result, primitive scratch and encoded native partial work. Generic height
arithmetic suffices; no runtime lattice or height observer is introduced. -/
namespace Blotto.GeneralPaperAffineValueStorage
open RationalOrderCell GeneralPaperRayAffine GeneralPaperRationalPrimitivePrice
open GeneralPaperAffineWitnessStorage GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def height (R s : ℕ) : ℕ := 2*R+s+1
def price (model : RationalCostModel) (R s : ℕ) : ℕ := model.rat (1+2*height R s)
def workCap (model : RationalCostModel) (W R s : ℕ) : ℕ := 16*W+4*price model R s

theorem operands (R s : ℕ) (f : Affine) (t : ℚ)
    (hi : RationalHeight f.intercept R) (hs : RationalHeight f.slope R) (ht : RationalHeight t s) :
    RationalHeight t (height R s) ∧ RationalHeight (f.slope*t) (height R s) ∧
      RationalHeight (GeneralPaperAffineValuePrice.run (fun w => w) 0 f t).1 (height R s) := by
  refine ⟨ht.mono (by unfold height; omega),(hs.mul ht).mono (by unfold height; omega),?_⟩
  simpa only [GeneralPaperAffineValuePrice.data,Affine.value,height,two_mul,Nat.add_assoc] using hi.add (hs.mul ht)

theorem primitives (model : RationalCostModel) (R s : ℕ) (f : Affine) (t : ℚ)
    (hi : RationalHeight f.intercept R) (hs : RationalHeight f.slope R) (ht : RationalHeight t s) :
    binary model.rat (·*·) f.slope t≤2*price model R s ∧
      binary model.rat (·+·) f.intercept (f.slope*t)≤2*price model R s := by
  have h := operands R s f t hi hs ht
  have hI := hi.mono (show R≤height R s by unfold height; omega)
  have hS := hs.mono (show R≤height R s by unfold height; omega)
  exact ⟨binary_le model.rat model.monotone (·*·) _ _ _ (rationalWordWidth_of_height hS)
      (rationalWordWidth_of_height h.1) (rationalWordWidth_of_height h.2.1),
    binary_le model.rat model.monotone (·+·) _ _ _ (rationalWordWidth_of_height hI)
      (rationalWordWidth_of_height h.2.1) (rationalWordWidth_of_height h.2.2)⟩

theorem work (model : RationalCostModel) (W R s : ℕ) (f : Affine) (t : ℚ)
    (hi : RationalHeight f.intercept R) (hs : RationalHeight f.slope R) (ht : RationalHeight t s) :
    (GeneralPaperAffineValuePrice.run model.rat W f t).2≤workCap model W R s := by
  have hp := primitives model R s f t hi hs ht
  change 16*W+binary model.rat (·*·) f.slope t+binary model.rat (·+·) f.intercept (f.slope*t)≤_
  unfold workCap
  omega

def window (model : RationalCostModel) (W : ℕ) (f : Affine) (t : ℚ) : ℕ :=
  let multiply := binary model.rat (·*·) f.slope t
  let add := binary model.rat (·+·) f.intercept (f.slope*t)
  let result := GeneralPaperAffineValuePrice.run model.rat W f t
  affineFoot W f+rationalWordWidth t+rationalWordWidth (f.slope*t)+rationalWordWidth result.1+multiply+add+
    fields W [16*W,multiply,add,16*W+multiply,result.2]+256*W

def profile (model : RationalCostModel) (W R s : ℕ) : ℕ :=
  affineProfile W R+3*(1+2*height R s)+4*price model R s+
    5*(natBits (1+workCap model W R s)+W)+288*W

theorem bounded (model : RationalCostModel) (W R s : ℕ) (f : Affine) (t : ℚ)
    (hi : RationalHeight f.intercept R) (hs : RationalHeight f.slope R) (ht : RationalHeight t s) :
    window model W f t≤profile model W R s := by
  let multiply := binary model.rat (·*·) f.slope t
  let add := binary model.rat (·+·) f.intercept (f.slope*t)
  let result := GeneralPaperAffineValuePrice.run model.rat W f t
  have hO := operands R s f t hi hs ht
  have hT := rationalWordWidth_of_height hO.1
  have hP := rationalWordWidth_of_height hO.2.1
  have hV := rationalWordWidth_of_height hO.2.2
  change rationalWordWidth result.1≤1+2*height R s at hV
  have hp := primitives model R s f t hi hs ht
  have ha := affine_bound W R f hi hs
  have hc := work model W R s f t hi hs ht
  change result.2≤workCap model W R s at hc
  have he : result.2=16*W+multiply+add := rfl
  have hf := fields_bound W (natBits (1+workCap model W R s)) [16*W,multiply,add,16*W+multiply,result.2] (by
    intro a ha
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl <;> omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤5*(natBits (1+workCap model W R s)+W)+32*W at hf
  change affineFoot W f+rationalWordWidth t+rationalWordWidth (f.slope*t)+rationalWordWidth result.1+multiply+add+
    GeneralPaperEncodedScalarStorage.fields W [16*W,multiply,add,16*W+multiply,result.2]+256*W≤_
  unfold profile
  rcases hp with ⟨hp1,hp2⟩
  change multiply≤2*price model R s at hp1
  change add≤2*price model R s at hp2
  omega

end Blotto.GeneralPaperAffineValueStorage
