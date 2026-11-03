import Blotto.GeneralPaperCircleCoefficientConstructionStorage

/-! Full owners and literal scalar frames of the native one-pass arc
constructor. Bounds inspect existing data only; no runtime census is added. -/
namespace Blotto.GeneralPaperCircleArcConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open GeneralPaperCircleArcMetadata
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

def price (model : RationalCostModel) (W N M : ℕ) : ℕ :=
  (N+1)*(64*W+8*model.rat (1+binaryWordWidth M))
def cap (model : RationalCostModel) (W N M R : ℕ) : ℕ :=
  N+M+R+price model W N M+64*W+1

def controls (model : RationalCostModel) (W R : ℕ) : List ℕ → ℕ → List ℕ
  | [],offset =>
    let copy := model.rat (GeneralPaperNaturalPrimitivePrice.word offset)
    [R,offset,offset,copy,16*W,(run model.rat W R [] offset).2]
  | w::tail,offset =>
    let len := R*w
    let later := run model.rat W R tail (offset+len)
    let mul := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) R w
    let add := GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) offset len
    let copy := model.rat (GeneralPaperNaturalPrimitivePrice.word offset)
    [R,w,offset,len,offset+len,later.1.total,later.2,(run model.rat W R (w::tail) offset).2,
      mul,add,copy,32*W,later.2+mul,later.2+mul+add,later.2+mul+add+copy,(w::tail).length]

def scratch (model : RationalCostModel) (W R : ℕ) : List ℕ → ℕ → ℕ
  | [],offset => model.rat (GeneralPaperNaturalPrimitivePrice.word offset)+16*W
  | w::_,offset =>
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) R w+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) offset (R*w)+
    model.rat (GeneralPaperNaturalPrimitivePrice.word offset)+32*W

def frame (model : RationalCostModel) (W R : ℕ) (xs : List ℕ) (offset : ℕ) : ℕ :=
  fields W (controls model W R xs offset)+scratch model W R xs offset+128*W

def frameProfile (model : RationalCostModel) (W N M R : ℕ) : ℕ :=
  16*(natBits (cap model W N M R)+W)+5*model.rat (1+binaryWordWidth M)+192*W

theorem work (model : RationalCostModel) (W N M R : ℕ) (xs : List ℕ) (offset : ℕ)
    (hn : xs.length≤N) (hR : R≤M) (ht : offset+R*xs.sum≤M)
    (hw : ∀ w∈xs,w≤M) : (run model.rat W R xs offset).2≤price model W N M := by
  exact (work_bound model.rat model.monotone W R xs offset M hR ht hw).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right hn 1))

theorem frame_bound (model : RationalCostModel) (W N M R : ℕ) (xs : List ℕ) (offset : ℕ)
    (hn : xs.length≤N) (hR : R≤M) (ht : offset+R*xs.sum≤M)
    (hw : ∀ w∈xs,w≤M) : frame model W R xs offset≤frameProfile model W N M R := by
  have hWork := work model W N M R xs offset hn hR ht hw
  have hOff : offset≤M := by omega
  have hCopy := model.monotone (Nat.add_le_add_left (binaryWordWidth_mono hOff) 1)
  change model.rat (GeneralPaperNaturalPrimitivePrice.word offset)≤model.rat (1+binaryWordWidth M) at hCopy
  cases xs with
  | nil =>
    have hf := fields_bound W (natBits (cap model W N M R)) (controls model W R [] offset) (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hz
      have hShape : (run model.rat W R [] offset).2=16*W+model.rat (GeneralPaperNaturalPrimitivePrice.word offset) := rfl
      unfold cap
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
    change fields W _≤6*(natBits (cap model W N M R)+W)+32*W at hf
    unfold frame frameProfile
    simp only [scratch]
    omega
  | cons w tail =>
    have hWgt := hw w List.mem_cons_self
    have hTail : offset+R*w+R*tail.sum≤M := by
      simp only [List.sum_cons] at ht
      nlinarith only [ht]
    have hLen : R*w≤M := by omega
    have hNext : offset+R*w≤M := by omega
    have hTotal : (run model.rat W R tail (offset+R*w)).1.total≤M := by
      rw [total];exact hTail
    have hMul := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a*b) R w M hR hWgt hLen
    have hAdd := GeneralPaperNaturalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a+b) offset (R*w) M hOff hLen hNext
    have hShape : (run model.rat W R (w::tail) offset).2=
      (run model.rat W R tail (offset+R*w)).2+
      GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a*b) R w+
      GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) offset (R*w)+
      model.rat (GeneralPaperNaturalPrimitivePrice.word offset)+32*W := rfl
    have hf := fields_bound W (natBits (cap model W N M R)) (controls model W R (w::tail) offset) (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold cap
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
    change fields W _≤16*(natBits (cap model W N M R)+W)+32*W at hf
    unfold frame frameProfile
    simp only [scratch]
    omega

def frames (model : RationalCostModel) (W R : ℕ) : List ℕ → ℕ → ℕ
  | [],offset => frame model W R [] offset
  | w::tail,offset => frame model W R (w::tail) offset+frames model W R tail (offset+R*w)

theorem frames_bound (model : RationalCostModel) (W N M R : ℕ) (xs : List ℕ) (offset : ℕ)
    (hn : xs.length≤N) (hR : R≤M) (ht : offset+R*xs.sum≤M)
    (hw : ∀ w∈xs,w≤M) : frames model W R xs offset≤(xs.length+1)*frameProfile model W N M R := by
  induction xs generalizing offset with
  | nil => simpa only [frames,List.length_nil,Nat.zero_add,Nat.one_mul] using frame_bound model W N M R [] offset hn hR ht hw
  | cons w tail ih =>
    have hf := frame_bound model W N M R (w::tail) offset hn hR ht hw
    have hTail : offset+R*w+R*tail.sum≤M := by
      simp only [List.sum_cons] at ht
      nlinarith only [ht]
    have hi := ih (offset+R*w) (by simpa only [List.length_cons] using Nat.le_trans (Nat.le_succ _) hn)
      hTail (fun x hx => hw x (List.mem_cons_of_mem _ hx))
    change frame model W R (w::tail) offset+frames model W R tail (offset+R*w)≤_
    simp only [List.length_cons]
    nlinarith only [hf,hi]

def window (model : RationalCostModel) (W R : ℕ) (xs : List ℕ) (offset : ℕ) : ℕ :=
  let made := run model.rat W R xs offset
  listFootprint W natBits xs+listFootprint W (GeneralPaperCachedCircleRetainedStorage.arcBits W) made.1.arcs+
    frames model W R xs offset+fields W [xs.length,offset,made.1.total,made.2]+128*W

def profile (model : RationalCostModel) (W N M R : ℕ) : ℕ :=
  N*(natBits M+2*W)+32*W+N*(2*natBits M+34*W)+32*W+
    (N+1)*frameProfile model W N M R+4*(natBits (cap model W N M R)+W)+160*W

theorem bounded (model : RationalCostModel) (W N M R : ℕ) (xs : List ℕ) (offset : ℕ)
    (hn : xs.length≤N) (hR : R≤M) (ht : offset+R*xs.sum≤M)
    (hw : ∀ w∈xs,w≤M) : window model W R xs offset≤profile model W N M R := by
  have hi := list_bound W (natBits M) natBits xs (fun w hm => Nat.add_le_add_left (binaryWordWidth_mono (hw w hm)) 1)
  have hTotal : (run model.rat W R xs offset).1.total≤M := by rw [total];exact ht
  have ho := list_bound W (2*natBits M+32*W) (GeneralPaperCachedCircleRetainedStorage.arcBits W)
    (run model.rat W R xs offset).1.arcs (by
      intro arc ha
      have hr := (ranges model.rat W R xs offset arc ha).trans hTotal
      have h1 := binaryWordWidth_mono (show arc.1≤M by omega)
      have h2 := binaryWordWidth_mono (show arc.2≤M by omega)
      unfold GeneralPaperCachedCircleRetainedStorage.arcBits natBits
      omega)
  rw [length] at ho
  have hFrames := frames_bound model W N M R xs offset hn hR ht hw
  have hWork := work model W N M R xs offset hn hR ht hw
  have hf := fields_bound W (natBits (cap model W N M R))
    [xs.length,offset,(run model.rat W R xs offset).1.total,(run model.rat W R xs offset).2] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold cap
      rcases hz with rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤4*(natBits (cap model W N M R)+W)+32*W at hf
  have hiN := Nat.mul_le_mul_right (natBits M+2*W) hn
  have hoN := Nat.mul_le_mul_right (2*natBits M+34*W) hn
  have hfN := Nat.mul_le_mul_right (frameProfile model W N M R) (Nat.add_le_add_right hn 1)
  unfold window profile
  dsimp only
  nlinarith only [hi,ho,hFrames,hf,hiN,hoN,hfN]

end Blotto.GeneralPaperCircleArcConstructionStorage
