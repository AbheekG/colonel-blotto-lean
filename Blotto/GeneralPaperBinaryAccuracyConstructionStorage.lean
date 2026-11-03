import Blotto.GeneralPaperAccuracyCountConstructionStorage

/-! Complete actual Boolean-word accuracy preparation. Existing Boolean
cancellation/alignment/comparison feeds the native natural counter once.
Both input words, ruler data, all data/work frames and caller partial/work
fields remain visible. Widths/caps here are erased analysis only. -/
namespace Blotto.GeneralPaperBinaryAccuracyConstructionStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

def inputSize (words : BinaryAccuracyWords) : ℕ := words.denominator.width+words.numerator.width

def price (W E : ℕ) : ℕ := 32*(E+1)*W+GeneralPaperAccuracyCountConstructionStorage.price W E+64*W

def cap (W E : ℕ) : ℕ := E+32*(E+1)+price W E+64*W+W+1

def controls (W : ℕ) (words : BinaryAccuracyWords) : List ℕ :=
  let ruler := BinaryRulerPrecisionWork.prepareWithWork words.denominator words.numerator
  let selected := GeneralPaperBinaryAccuracy.count (fun w => w) W ruler.1
  [W,ruler.2,selected.1,selected.2,ruler.2*W,ruler.2*W+selected.2,64*W,
    (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).2]

def window (W : ℕ) (words : BinaryAccuracyWords) : ℕ :=
  let ruler := BinaryRulerPrecisionWork.prepareWithWork words.denominator words.numerator
  GeneralPaperBooleanRulerWorkStorage.window W words.denominator words.numerator+
    GeneralPaperAccuracyCountConstructionStorage.window W ruler.1+fields W (controls W words)+128*W

def profile (W E : ℕ) : ℕ :=
  GeneralPaperBooleanRulerWorkStorage.profile W E+GeneralPaperAccuracyCountConstructionStorage.profile W E+
    8*(natBits (cap W E)+W)+160*W

theorem ruler_length (words : BinaryAccuracyWords) :
    (BinaryRulerPrecisionWork.prepareWithWork words.denominator words.numerator).1.length≤words.denominator.width := by
  rw [BinaryRulerPrecisionWork.prepare_state,BinaryRulerPrecisionLifetime.prepareWithTrace_state]
  exact BinaryRulerPrecision.prepare_length_bound _ _

theorem work (W : ℕ) (words : BinaryAccuracyWords) :
    (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).2≤price W (inputSize words) := by
  have hr := BinaryRulerPrecisionWork.prepare_work words.denominator words.numerator
  have hl := ruler_length words
  have hc := GeneralPaperAccuracyCountConstructionStorage.work_cap W (inputSize words)
    (BinaryRulerPrecisionWork.prepareWithWork words.denominator words.numerator).1 (by unfold inputSize;omega)
  have hw := Nat.mul_le_mul_right W hr
  unfold GeneralPaperBinaryAccuracy.prepare price
  dsimp only
  change _≤32*(inputSize words+1)*W+GeneralPaperAccuracyCountConstructionStorage.price W (inputSize words)+64*W
  change _≤32*(inputSize words+1)*W at hw
  omega

theorem bounded (W : ℕ) (words : BinaryAccuracyWords) : window W words≤profile W (inputSize words) := by
  let E := inputSize words
  let r := BinaryRulerPrecisionWork.prepareWithWork words.denominator words.numerator
  let c := GeneralPaperBinaryAccuracy.count (fun w => w) W r.1
  have hR := GeneralPaperBooleanRulerWorkStorage.bounded W words.denominator words.numerator
  have hL : r.1.length≤E := by have h:=ruler_length words;dsimp only [E,inputSize,r];omega
  have hC := GeneralPaperAccuracyCountConstructionStorage.bounded W E r.1 hL
  have hRW := BinaryRulerPrecisionWork.prepare_work words.denominator words.numerator
  have hCW := GeneralPaperAccuracyCountConstructionStorage.work_cap W E r.1 hL
  have hCount : c.1≤E := by rw [GeneralPaperBinaryAccuracy.count_data];exact hL
  have hw := work W words
  have hShape : (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).2=r.2*W+c.2+64*W := rfl
  have hf := fields_bound W (natBits (cap W E)) (controls W words) (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold cap
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only [r,c,E,inputSize] at * <;> omega)
  change fields W _≤8*(natBits (cap W E)+W)+32*W at hf
  unfold window profile
  dsimp only [E,r,c,inputSize] at *
  omega

theorem rational_input_size (epsilon : ℚ) (hE : 0<epsilon) (words : BinaryAccuracyWords)
    (hNumeric : words.numeric=GeneralPaperBinaryAccuracy.input epsilon hE) :
    inputSize words+1=rationalWordWidth epsilon := by
  have hn := congrArg BinaryAccuracyInput.numerator hNumeric
  have hd := congrArg BinaryAccuracyInput.denominator hNumeric
  change words.numerator.value=epsilon.num.toNat at hn
  change words.denominator.value=epsilon.den at hd
  have hp : 0<epsilon.num := Rat.num_pos.mpr hE
  have ha : epsilon.num.toNat=epsilon.num.natAbs := by omega
  unfold inputSize rationalWordWidth
  rw [words.denominator.width_eq,words.numerator.width_eq,hn,hd,ha]
  omega

theorem rational_input_contract (W : ℕ) (epsilon : ℚ) (hE : 0<epsilon) (words : BinaryAccuracyWords)
    (hNumeric : words.numeric=GeneralPaperBinaryAccuracy.input epsilon hE) :
    (GeneralPaperBinaryAccuracy.prepare (fun w => w) W words).1=(GeneralPaperDyadicAccuracy.prepare epsilon).exponent ∧
      window W words≤profile W (inputSize words) ∧ inputSize words+1=rationalWordWidth epsilon := by
  have hn := congrArg BinaryAccuracyInput.numerator hNumeric
  have hd := congrArg BinaryAccuracyInput.denominator hNumeric
  have hValue : epsilon=(words.numerator.value:ℚ)/words.denominator.value := by
    rw [show words.numerator.value=(GeneralPaperBinaryAccuracy.input epsilon hE).numerator from hn,
      show words.denominator.value=(GeneralPaperBinaryAccuracy.input epsilon hE).denominator from hd]
    exact (GeneralPaperBinaryAccuracy.input_value epsilon hE).symm
  exact ⟨GeneralPaperBinaryAccuracy.exact_exponent (fun w => w) W words epsilon hValue,
    bounded W words,rational_input_size epsilon hE words hNumeric⟩

theorem encoded_word_contract (W : ℕ) (epsilon : ℚ) (hE : 0<epsilon) (suffix : List Bool) :
    ∃ parsed,(GeneralPaperBinaryAccuracy.read (fun w => w) W
        (BinaryAccuracyFrame.encode (GeneralPaperBinaryAccuracy.input epsilon hE)++suffix)).1=some (parsed,suffix) ∧
      parsed.exponent=(GeneralPaperDyadicAccuracy.prepare epsilon).exponent ∧
      window W parsed.words≤profile W (inputSize parsed.words) ∧ inputSize parsed.words+1=rationalWordWidth epsilon := by
  obtain ⟨parsed,hr,hn⟩ := GeneralPaperBinaryAccuracy.read_complete (fun w => w) W
    (GeneralPaperBinaryAccuracy.input epsilon hE) suffix
  have hc := rational_input_contract W epsilon hE parsed.words hn
  refine ⟨parsed,hr,?_,hc.2⟩
  rw [parsed.correct,←GeneralPaperBinaryAccuracy.prepare_data (fun w => w) W parsed.words]
  exact hc.1

@[fun_prop]
theorem scaling (E : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => profile W E) := by
  unfold profile cap price GeneralPaperAccuracyCountConstructionStorage.price GeneralPaperAccuracyCountConstructionStorage.step
  fun_prop

open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperCacheConstructionGrowth

theorem profile_rate (W E : Input → ℕ) (hW : Tight W) (hE : Small E) : Linear (fun x => profile (W x) (E x)) E := by
  have hw := of_tight hW
  have hWP := poly_tight W hW
  have hR := GeneralPaperBooleanRulerWorkStorage.profile_rate W E hW hE
  have hC := GeneralPaperAccuracyCountConstructionStorage.profile_rate W E hW hE
  have hPrice : Small (fun x => price (W x) (E x)) := by
    unfold price GeneralPaperAccuracyCountConstructionStorage.price GeneralPaperAccuracyCountConstructionStorage.step
      GeneralPaperAccuracyCountConstructionStorage.width
    fun_prop
  have hTail : Polylog (fun x => 8*(natBits (cap (W x) (E x))+W x)+160*W x) := by
    unfold cap natBits
    fun_prop
  have hT := linear_poly _ E hTail
  simpa only [profile,Nat.add_assoc] using linear_add _ _ E (linear_add _ _ E hR hC) hT

theorem window_rate (W : Input → ℕ) (words : Input → BinaryAccuracyWords) (hW : Tight W)
    (hE : Small (fun x => inputSize (words x))) :
    Linear (fun x => window (W x) (words x)) (fun x => inputSize (words x)) :=
  GeneralPaperSourceSoftBounds.dominated (profile_rate W (fun x => inputSize (words x)) hW hE)
    (fun x => bounded (W x) (words x))

end Blotto.GeneralPaperBinaryAccuracyConstructionStorage
