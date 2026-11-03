import Blotto.GeneralPaperMidpointRawBits

/-! Final inclusive root-cell or strict source-bucket tests on the retained
CF result. Endpoint/selected-fraction casts, natural successor, three rational
divisions, both comparisons and the result record are explicitly priced.
-/
namespace Blotto.GeneralPaperMidpointFilterBits
open GeneralPaperRegularCFLoop GeneralPaperCFOperandBounds
set_option autoImplicit false
set_option maxHeartbeats 8000000

def upperValue (C t : ℕ) : ℚ := ((t+1:ℕ):ℚ)/(C:ℚ)

def accepts (closed : Bool) (C t : ℕ) (f : Farey.Fraction) : Bool :=
  let scale : ℚ := C
  let lowerValue := (t:ℚ)/scale
  let upperValue := ((t+1:ℕ):ℚ)/scale
  let selectedValue := f.value
  if closed then decide (lowerValue≤selectedValue ∧ selectedValue≤upperValue)
    else decide (lowerValue<selectedValue ∧ selectedValue<upperValue)

def filter (closed : Bool) (C t : ℕ) (s : State) : GeneralPaperMidpointQuery.Result :=
  ⟨s.selected.bind (fun f => if accepts closed C t f then some f else none),s.work+32,s.steps,s.quotientDepth⟩

theorem closed_data (D C t lambda : ℕ) :
    filter true C t (GeneralPaperMidpointQuery.raw D C t lambda)=GeneralPaperProxyRootQuery.lookup D C t lambda := by
  simp only [filter,accepts,GeneralPaperProxyRootQuery.lookup,GeneralPaperBucketGeometry.lower,
    GeneralPaperBucketGeometry.upper,ite_true,Nat.cast_add,Nat.cast_one,decide_eq_true_eq]
  rfl

theorem strict_data (D C t lambda : ℕ) :
    filter false C t (GeneralPaperMidpointQuery.raw D C t lambda)=GeneralPaperMidpointQuery.lookup D C t lambda := by
  simp only [filter,accepts,GeneralPaperMidpointQuery.lookup,GeneralPaperBucketGeometry.lower,
    GeneralPaperBucketGeometry.upper,Bool.false_eq_true,ite_false,Nat.cast_add,Nat.cast_one,decide_eq_true_eq]
  rfl

def operandWork (model : RationalCostModel) (C t : ℕ) (f : Farey.Fraction) : ℕ :=
  model.rat (rationalWordWidth (t:ℚ))+model.rat (rationalWordWidth (C:ℚ))+
  model.rat (rationalWordWidth ((t+1:ℕ):ℚ))+model.rat (rationalWordWidth (f.num:ℚ))+
  model.rat (rationalWordWidth (f.den:ℚ))+
  GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) t 1+
  GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) (t:ℚ) (C:ℚ)+
  GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) ((t+1:ℕ):ℚ) (C:ℚ)+
  GeneralPaperRationalPrimitivePrice.binary model.rat (fun a b => a/b) (f.num:ℚ) (f.den:ℚ)+
  GeneralPaperBoundedQuotient.primitivePrice model ((t:ℚ)/(C:ℚ)) f.value+
  GeneralPaperBoundedQuotient.primitivePrice model f.value (upperValue C t)

theorem operand_work (model : RationalCostModel) (D C t lambda : ℕ) (f : Farey.Fraction)
    (ht : t<C) (hM : 2*C<2^lambda) (hNum : f.num≤2*t+1) (hDen : f.den≤2*C) :
    operandWork model C t f≤15*model.rat (GeneralPaperCFOperandPrice.width lambda D) := by
  let L := GeneralPaperCFOperandPrice.width lambda D
  let P := model.rat L
  have height (x : ℕ) (hx : x<2^lambda) : RationalHeight (x:ℚ) (lambda+1) :=
    (GeneralPaperBasisDivideBits.nat_height x).mono (GeneralPaperCFOperandPrice.small_word lambda x hx)
  have hj := height t (by omega)
  have hC := height C (by omega)
  have hJ := height (t+1) (by omega)
  have hfN := height f.num (by omega)
  have hfD := height f.den (hDen.trans_lt hM)
  have word_cast (x : ℕ) (h : RationalHeight (x:ℚ) (lambda+1)) : rationalWordWidth (x:ℚ)≤L :=
    (rationalWordWidth_of_height h).trans (by dsimp [L,GeneralPaperCFOperandPrice.width]; omega)
  have wj := word_cast t hj
  have wC := word_cast C hC
  have wJ := word_cast (t+1) hJ
  have wfN := word_cast f.num hfN
  have wfD := word_cast f.den hfD
  have wLo : rationalWordWidth ((t:ℚ)/(C:ℚ))≤L :=
    (rationalWordWidth_of_height (hj.div hC)).trans (by dsimp [L,GeneralPaperCFOperandPrice.width]; omega)
  have wHi : rationalWordWidth (upperValue C t)≤L :=
    (rationalWordWidth_of_height (hJ.div hC)).trans (by dsimp [L,GeneralPaperCFOperandPrice.width]; omega)
  have wVal : rationalWordWidth f.value≤L :=
    (rationalWordWidth_of_height (hfN.div hfD)).trans (by dsimp [L,GeneralPaperCFOperandPrice.width]; omega)
  have c1 := model.monotone wj
  have c2 := model.monotone wC
  have c3 := model.monotone wJ
  have c4 := model.monotone wfN
  have c5 := model.monotone wfD
  have wjN := GeneralPaperCFOperandPrice.small_word lambda t (by omega : t<2^lambda)
  have wJN := GeneralPaperCFOperandPrice.small_word lambda (t+1) (by omega : t+1<2^lambda)
  have h1 : binaryWordWidth 1=1 := by decide
  have c6 := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a+b) t 1 L
    (by dsimp [L,GeneralPaperCFOperandPrice.width]; omega)
    (by dsimp [L,GeneralPaperCFOperandPrice.width]; omega)
    (by dsimp [L,GeneralPaperCFOperandPrice.width]; omega)
  have c7 := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b) (t:ℚ) (C:ℚ) L wj wC wLo
  have c8 := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b) ((t+1:ℕ):ℚ) (C:ℚ) L wJ wC wHi
  have c9 := GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone (fun a b => a/b) (f.num:ℚ) (f.den:ℚ) L wfN wfD wVal
  have c10 := GeneralPaperBoundedQuotient.primitivePrice_le model ((t:ℚ)/(C:ℚ)) f.value L wLo wVal
  have c11 := GeneralPaperBoundedQuotient.primitivePrice_le model f.value (upperValue C t) L wVal wHi
  change operandWork model C t f≤15*P
  unfold operandWork
  omega

def run (model : RationalCostModel) (W : ℕ) (closed : Bool) (C t : ℕ) (s : State) : GeneralPaperMidpointQuery.Result × ℕ :=
  (filter closed C t s,match s.selected with | none => 64*W | some f => operandWork model C t f+96*W)

theorem work (model : RationalCostModel) (W D C t lambda : ℕ) (closed : Bool) (s : State)
    (h : Valid lambda (2*t+1) (2*C) s) (ht : t<C) (hM : 2*C<2^lambda) :
    (run model W closed C t s).2≤96*W+15*model.rat (GeneralPaperCFOperandPrice.width lambda D) := by
  cases hs : s.selected with
  | none =>
    change (match s.selected with | none => 64*W | some f => operandWork model C t f+96*W)≤_
    rw [hs]
    dsimp only
    omega
  | some f =>
    have hf := h.selected f hs
    have hw := operand_work model D C t lambda f ht hM hf.1 hf.2
    change (match s.selected with | none => 64*W | some f => operandWork model C t f+96*W)≤_
    rw [hs]
    dsimp only
    omega

end Blotto.GeneralPaperMidpointFilterBits
