import Blotto.GeneralPaperPositiveWordReadConstructionStorage

/-! Both native positive-word reads and the once-only Boolean-word accuracy
selector, with full returned words/suffix/exponent and parent work fields.
Only the branch selected by the actual native reads is observed. -/
namespace Blotto.GeneralPaperFramedAccuracyConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperBooleanRulerWorkStorage
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384

theorem word_price_mono (W E F : ℕ) (h : E≤F) :
    GeneralPaperBinaryAccuracyConstructionStorage.price W E≤GeneralPaperBinaryAccuracyConstructionStorage.price W F := by
  unfold GeneralPaperBinaryAccuracyConstructionStorage.price GeneralPaperAccuracyCountConstructionStorage.price
    GeneralPaperAccuracyCountConstructionStorage.step GeneralPaperAccuracyCountConstructionStorage.width
  gcongr

theorem word_profile_mono (W E F : ℕ) (h : E≤F) :
    GeneralPaperBinaryAccuracyConstructionStorage.profile W E≤GeneralPaperBinaryAccuracyConstructionStorage.profile W F := by
  unfold GeneralPaperBinaryAccuracyConstructionStorage.profile GeneralPaperBinaryAccuracyConstructionStorage.cap
    GeneralPaperBinaryAccuracyConstructionStorage.price GeneralPaperBooleanRulerWorkStorage.profile budget
    GeneralPaperAccuracyCountConstructionStorage.profile GeneralPaperAccuracyCountConstructionStorage.frameProfile
    GeneralPaperAccuracyCountConstructionStorage.cap GeneralPaperAccuracyCountConstructionStorage.price
    GeneralPaperAccuracyCountConstructionStorage.step GeneralPaperAccuracyCountConstructionStorage.width natBits
  gcongr

def price (W E : ℕ) : ℕ := 4*(E+1)*W+GeneralPaperBinaryAccuracyConstructionStorage.price W E+64*W

def cap (W E : ℕ) : ℕ := E+4*(E+1)+price W E+64*W+W+1

def secondWindow (W : ℕ) (frame : List Bool) : ℕ :=
  match (BinaryPositiveWordReadWork.read frame).1 with
  | none => 0
  | some numerator => GeneralPaperPositiveWordReadConstructionStorage.window W numerator.2

def selectedWindow (W : ℕ) (frame : List Bool) : ℕ :=
  match (BinaryPositiveWordReadWork.read frame).1 with
  | none => 0
  | some numerator => match (BinaryPositiveWordReadWork.read numerator.2).1 with
    | none => 0
    | some denominator => GeneralPaperBinaryAccuracyConstructionStorage.window W ⟨numerator.1,denominator.1⟩

def returnedFoot (W : ℕ) (frame : List Bool) : ℕ :=
  match (GeneralPaperBinaryAccuracy.read (fun w => w) W frame).1 with
  | none => 0
  | some parsed => wordFoot W parsed.1.words.numerator+wordFoot W parsed.1.words.denominator+
      listFootprint W (fun _ : Bool => 1) parsed.2+fields W [parsed.1.exponent]+64*W

def returnProfile (W E : ℕ) : ℕ := E*(1+2*W)+natBits E+384*W

def controls (W : ℕ) (frame : List Bool) : List ℕ :=
  let first := BinaryPositiveWordReadWork.read frame
  [W,first.2]++match first.1 with
  | none => [first.2*W,64*W,(GeneralPaperBinaryAccuracy.read (fun w => w) W frame).2]
  | some numerator =>
    let second := BinaryPositiveWordReadWork.read numerator.2
    [second.2,first.2+second.2,(first.2+second.2)*W]++match second.1 with
    | none => [64*W,(GeneralPaperBinaryAccuracy.read (fun w => w) W frame).2]
    | some denominator =>
      let selected := GeneralPaperBinaryAccuracy.prepare (fun w => w) W (⟨numerator.1,denominator.1⟩:BinaryAccuracyWords)
      [selected.1,selected.2,(first.2+second.2)*W+selected.2,64*W,(GeneralPaperBinaryAccuracy.read (fun w => w) W frame).2]

def window (W : ℕ) (frame : List Bool) : ℕ :=
  GeneralPaperPositiveWordReadConstructionStorage.window W frame+secondWindow W frame+selectedWindow W frame+
    returnedFoot W frame+fields W (controls W frame)+128*W

def profile (W E : ℕ) : ℕ :=
  2*GeneralPaperPositiveWordReadConstructionStorage.profile W E+GeneralPaperBinaryAccuracyConstructionStorage.profile W E+
    returnProfile W E+10*(natBits (cap W E)+W)+160*W

theorem parsed_size (E : ℕ) (frame : List Bool) (numerator denominator : PositiveBinaryWord×List Bool)
    (hc : frame.length≤E) (hN : (BinaryPositiveWordReadWork.read frame).1=some numerator)
    (hD : (BinaryPositiveWordReadWork.read numerator.2).1=some denominator) :
    GeneralPaperBinaryAccuracyConstructionStorage.inputSize (⟨numerator.1,denominator.1⟩:BinaryAccuracyWords)+denominator.2.length≤E := by
  have hn := BinaryPositiveWordReadWork.read_consumed frame numerator hN
  have hd := BinaryPositiveWordReadWork.read_consumed numerator.2 denominator hD
  unfold GeneralPaperBinaryAccuracyConstructionStorage.inputSize
  dsimp only
  omega

theorem second_bounded (W E : ℕ) (frame : List Bool) (hc : frame.length≤E) :
    secondWindow W frame≤GeneralPaperPositiveWordReadConstructionStorage.profile W E := by
  unfold secondWindow
  cases hn:(BinaryPositiveWordReadWork.read frame).1 with
  | none => dsimp only;omega
  | some numerator =>
    dsimp only
    have hl := BinaryPositiveWordReadWork.read_suffix_length frame numerator hn
    exact GeneralPaperPositiveWordReadConstructionStorage.bounded W E numerator.2 (hl.trans hc)

theorem selected_bounded (W E : ℕ) (frame : List Bool) (hc : frame.length≤E) :
    selectedWindow W frame≤GeneralPaperBinaryAccuracyConstructionStorage.profile W E := by
  unfold selectedWindow
  cases hn:(BinaryPositiveWordReadWork.read frame).1 with
  | none => dsimp only;omega
  | some numerator =>
    dsimp only
    cases hd:(BinaryPositiveWordReadWork.read numerator.2).1 with
    | none => dsimp only;omega
    | some denominator =>
      have hs := parsed_size E frame numerator denominator hc hn hd
      exact (GeneralPaperBinaryAccuracyConstructionStorage.bounded W ⟨numerator.1,denominator.1⟩).trans
        (word_profile_mono W _ E (by omega))

theorem work (W E : ℕ) (frame : List Bool) (hc : frame.length≤E) :
    (GeneralPaperBinaryAccuracy.read (fun w => w) W frame).2≤price W E := by
  have hf := BinaryPositiveWordReadWork.read_bound frame
  unfold GeneralPaperBinaryAccuracy.read
  dsimp only
  cases hn:(BinaryPositiveWordReadWork.read frame).1 with
  | none =>
    dsimp only
    have hp := Nat.mul_le_mul_right W (show (BinaryPositiveWordReadWork.read frame).2≤4*(E+1) by omega)
    unfold price
    omega
  | some numerator =>
    dsimp only
    have hl := BinaryPositiveWordReadWork.read_suffix_length frame numerator hn
    have hd := BinaryPositiveWordReadWork.read_bound numerator.2
    have hp := Nat.mul_le_mul_right W (show (BinaryPositiveWordReadWork.read frame).2+
      (BinaryPositiveWordReadWork.read numerator.2).2≤4*(E+1) by omega)
    cases hd':(BinaryPositiveWordReadWork.read numerator.2).1 with
    | none => dsimp only;unfold price;omega
    | some denominator =>
      have hs := parsed_size E frame numerator denominator hc hn hd'
      have hw := (GeneralPaperBinaryAccuracyConstructionStorage.work W (⟨numerator.1,denominator.1⟩:BinaryAccuracyWords)).trans
        (word_price_mono W _ E (by omega))
      dsimp only
      unfold price
      omega

theorem returned_bound (W E : ℕ) (frame : List Bool) (hc : frame.length≤E) : returnedFoot W frame≤returnProfile W E := by
  unfold returnedFoot GeneralPaperBinaryAccuracy.read
  dsimp only
  cases hn:(BinaryPositiveWordReadWork.read frame).1 with
  | none => dsimp only;unfold returnProfile;omega
  | some numerator =>
    dsimp only
    cases hd:(BinaryPositiveWordReadWork.read numerator.2).1 with
    | none => dsimp only;unfold returnProfile;omega
    | some denominator =>
      have hs := parsed_size E frame numerator denominator hc hn hd
      have ha := word_bound W numerator.1
      have hb := word_bound W denominator.1
      have hSuffix := list_bound W 1 (fun _ : Bool => 1) denominator.2 (fun _ _ => le_rfl)
      have hK := GeneralPaperBinaryAccuracy.exponent_bound (fun w => w) W (⟨numerator.1,denominator.1⟩:BinaryAccuracyWords)
      have hdWidth : denominator.1.width≤E := by dsimp only [GeneralPaperBinaryAccuracyConstructionStorage.inputSize] at hs;omega
      have hWords := Nat.mul_le_mul_right (1+2*W) hs
      have hFields := fields_bound W (natBits E)
        [(GeneralPaperBinaryAccuracy.prepare (fun w => w) W (⟨numerator.1,denominator.1⟩:BinaryAccuracyWords)).1] (by
          intro z hz
          apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
          rw [hz]
          exact hK.trans hdWidth)
      dsimp only
      unfold returnProfile
      dsimp only [GeneralPaperBinaryAccuracyConstructionStorage.inputSize] at hWords
      simp only [List.length_cons,List.length_nil] at hFields
      nlinarith only [ha,hb,hSuffix,hWords,hFields]

theorem header_bound (W E : ℕ) (frame : List Bool) (hc : frame.length≤E) :
    fields W (controls W frame)≤10*(natBits (cap W E)+W)+32*W := by
  have hWork := work W E frame hc
  have hFirst := BinaryPositiveWordReadWork.read_bound frame
  have hLength : (controls W frame).length≤10 := by
    unfold controls
    dsimp only
    split
    · norm_num
    · split <;> norm_num
  have hf := fields_bound W (natBits (cap W E)) (controls W frame) (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    cases hn:(BinaryPositiveWordReadWork.read frame).1 with
    | none =>
      have hShape : (GeneralPaperBinaryAccuracy.read (fun w => w) W frame).2=(BinaryPositiveWordReadWork.read frame).2*W+64*W := by
        simp only [GeneralPaperBinaryAccuracy.read,hn]
      unfold controls at hz
      dsimp only at hz
      rw [hn] at hz
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold cap
      rcases hz with (rfl|rfl)|(rfl|rfl|rfl) <;> omega
    | some numerator =>
      have hSuffix := BinaryPositiveWordReadWork.read_suffix_length frame numerator hn
      have hSecond := BinaryPositiveWordReadWork.read_bound numerator.2
      unfold controls at hz
      dsimp only at hz
      rw [hn] at hz
      dsimp only at hz
      cases hd:(BinaryPositiveWordReadWork.read numerator.2).1 with
      | none =>
        have hShape : (GeneralPaperBinaryAccuracy.read (fun w => w) W frame).2=
            ((BinaryPositiveWordReadWork.read frame).2+(BinaryPositiveWordReadWork.read numerator.2).2)*W+64*W := by
          simp only [GeneralPaperBinaryAccuracy.read,hn,hd]
        rw [hd] at hz
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
        unfold cap
        rcases hz with (rfl|rfl)|((rfl|rfl|rfl)|(rfl|rfl)) <;> omega
      | some denominator =>
        have hSize := parsed_size E frame numerator denominator hc hn hd
        have hK := GeneralPaperBinaryAccuracy.exponent_bound (fun w => w) W (⟨numerator.1,denominator.1⟩:BinaryAccuracyWords)
        change (GeneralPaperBinaryAccuracy.prepare (fun w => w) W (⟨numerator.1,denominator.1⟩:BinaryAccuracyWords)).1≤denominator.1.width at hK
        have hShape : (GeneralPaperBinaryAccuracy.read (fun w => w) W frame).2=
            ((BinaryPositiveWordReadWork.read frame).2+(BinaryPositiveWordReadWork.read numerator.2).2)*W+
              (GeneralPaperBinaryAccuracy.prepare (fun w => w) W (⟨numerator.1,denominator.1⟩:BinaryAccuracyWords)).2+64*W := by
          simp only [GeneralPaperBinaryAccuracy.read,hn,hd]
        rw [hd] at hz
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
        unfold cap
        dsimp only [GeneralPaperBinaryAccuracyConstructionStorage.inputSize] at hSize
        rcases hz with (rfl|rfl)|((rfl|rfl|rfl)|(rfl|rfl|rfl|rfl|rfl)) <;> omega)
  exact hf.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hLength) _)

theorem bounded (W E : ℕ) (frame : List Bool) (hc : frame.length≤E) : window W frame≤profile W E := by
  have hFirst := GeneralPaperPositiveWordReadConstructionStorage.bounded W E frame hc
  have hSecond := second_bounded W E frame hc
  have hSelected := selected_bounded W E frame hc
  have hReturned := returned_bound W E frame hc
  have hHeader := header_bound W E frame hc
  unfold window profile
  omega

theorem returned_covered (W : ℕ) (frame : List Bool) : returnedFoot W frame≤window W frame := by unfold window;omega

theorem returned_bounded (W E : ℕ) (frame : List Bool) (hc : frame.length≤E) : returnedFoot W frame≤profile W E :=
  (returned_covered W frame).trans (bounded W E frame hc)

@[fun_prop]
theorem scaling (E : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => profile W E) := by
  unfold profile returnProfile cap price GeneralPaperBinaryAccuracyConstructionStorage.price
    GeneralPaperAccuracyCountConstructionStorage.price GeneralPaperAccuracyCountConstructionStorage.step
  fun_prop

open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperCacheConstructionGrowth

theorem profile_rate (W E : Input → ℕ) (hW : Tight W) (hE : Small E) : Linear (fun x => profile (W x) (E x)) E := by
  have hw := of_tight hW
  have hp := poly_tight W hW
  have hPos := GeneralPaperPositiveWordReadConstructionStorage.profile_rate W E hW hE
  have hWord := GeneralPaperBinaryAccuracyConstructionStorage.profile_rate W E hW hE
  have hPrice : Small (fun x => price (W x) (E x)) := by
    unfold price GeneralPaperBinaryAccuracyConstructionStorage.price GeneralPaperAccuracyCountConstructionStorage.price
      GeneralPaperAccuracyCountConstructionStorage.step GeneralPaperAccuracyCountConstructionStorage.width
    fun_prop
  have hTail : Polylog (fun x => 10*(natBits (cap (W x) (E x))+W x)+160*W x) := by
    unfold cap natBits
    fun_prop
  have hReturn : Linear (fun x => returnProfile (W x) (E x)) E := by
    unfold returnProfile natBits
    fun_prop
  have hTail' := linear_poly _ E hTail
  have hAll := linear_add _ _ E (linear_add _ _ E (linear_add _ _ E (linear_add _ _ E hPos hPos) hWord) hReturn) hTail'
  simpa only [profile,Nat.two_mul,Nat.add_assoc] using hAll

theorem window_rate (W : Input → ℕ) (frame : Input → List Bool) (hW : Tight W)
    (hE : Small (fun x => (frame x).length)) : Linear (fun x => window (W x) (frame x)) (fun x => (frame x).length) :=
  GeneralPaperSourceSoftBounds.dominated (profile_rate W (fun x => (frame x).length) hW hE)
    (fun x => bounded (W x) (frame x).length (frame x) le_rfl)

theorem canonical_frame_contract (W : ℕ) (epsilon : ℚ) (hE : 0<epsilon) (suffix : List Bool) :
    let frame := BinaryAccuracyFrame.encode (GeneralPaperBinaryAccuracy.input epsilon hE)++suffix
    ∃ parsed,(GeneralPaperBinaryAccuracy.read (fun w => w) W frame).1=some (parsed,suffix) ∧
      parsed.exponent=(GeneralPaperDyadicAccuracy.prepare epsilon).exponent ∧
      GeneralPaperBinaryAccuracyConstructionStorage.inputSize parsed.words+1=rationalWordWidth epsilon ∧
      window W frame≤profile W (2*rationalWordWidth epsilon+suffix.length) ∧
      returnedFoot W frame≤profile W (2*rationalWordWidth epsilon+suffix.length) := by
  obtain ⟨parsed,hr,hk,_,hSize⟩ := GeneralPaperBinaryAccuracyConstructionStorage.encoded_word_contract W epsilon hE suffix
  refine ⟨parsed,hr,hk,hSize,?_,?_⟩
  · apply bounded
    rw [List.length_append,GeneralPaperBinaryAccuracy.input_length]
  · apply returned_bounded
    rw [List.length_append,GeneralPaperBinaryAccuracy.input_length]

end Blotto.GeneralPaperFramedAccuracyConstructionStorage
