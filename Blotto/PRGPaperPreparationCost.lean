import Blotto.NativePRGRequestPreparation

/-! A single explicit fast envelope for the checked input, reference table,
raw accuracy selector and saved header. Rat retains its declared paper-model
meaning; no native library, allocator or compiler calibration is required. -/

namespace Blotto.PRGPaperPreparationCost
set_option autoImplicit false
set_option maxHeartbeats 2000000

def width (length : ℕ) : ℕ := 1024*(length+2)
def logFactor (length : ℕ) : ℕ := binaryWordWidth (9*length+13)+1
def bound (model : RationalCostModel) (c count length : ℕ) : ℕ :=
  1000000*(c+1)*(count+1)*(model.rat (width length)+(length+2)*logFactor length)

theorem component_bound (model : RationalCostModel) (c count length accuracyLength : ℕ)
    (hCount : count ≤ length) (hAccuracy : accuracyLength ≤ length) :
    NativePRGRequestPreparation.componentBound model c count length accuracyLength ≤
      bound model c count length := by
  let Q := logFactor length
  let G := (length+2)*Q
  let P := model.rat (width length)
  let N := count+1
  have hQ : 1 ≤ Q := by dsimp [Q,logFactor]; omega
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hG : length+2 ≤ G := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (length+2) hQ
  have hQG : Q ≤ G := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right Q (by omega : 1 ≤ length+2)
  have hGN : G ≤ N*G := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right G hN
  have hOne : 1 ≤ (c+1)*N*G := by
    exact Nat.mul_le_mul (Nat.mul_le_mul (by omega : 1 ≤ c+1) hN) (by omega : 1 ≤ G)
  have hLengthWord : binaryWordWidth (length+2) ≤ Q := by
    exact (binaryWordWidth_mono (by omega : length+2 ≤ 9*length+13)).trans (Nat.le_succ _)
  have hCountWord : binaryWordWidth (count+2) ≤ Q := by
    exact (binaryWordWidth_mono (by omega : count+2 ≤ 9*length+13)).trans (Nat.le_succ _)
  have hFirstWord : binaryWordWidth (count+1) ≤ Q :=
    (binaryWordWidth_mono (Nat.le_succ _)).trans hCountWord
  have hCountZero : binaryWordWidth count ≤ Q :=
    (binaryWordWidth_mono (Nat.le_succ _)).trans hFirstWord
  have hTableWord : binaryWordWidth (9*length+1)+1 ≤ Q := by
    exact Nat.add_le_add_right (binaryWordWidth_mono (by omega)) 1
  have hHeaderWord : binaryWordWidth count+1 ≤ length+2 := by
    have h := Nat.log2_le_self count
    unfold binaryWordWidth
    omega
  have hHeaderLog : binaryWordWidth (binaryWordWidth count+2)+1 ≤ Q := by
    apply Nat.add_le_add_right
    apply binaryWordWidth_mono
    have h := Nat.log2_le_self count
    unfold binaryWordWidth
    omega
  have hRat1 : model.rat (4*length+13) ≤ P := model.monotone (by unfold width; omega)
  have hRat2 : model.rat (32*(9*length+3)) ≤ P := model.monotone (by unfold width; omega)
  have hNat : BinarySequentialNatReadCost.price c length ≤ (96+16*c)*G := by
    unfold BinarySequentialNatReadCost.price
    simpa only [G,Nat.mul_assoc] using Nat.mul_le_mul_left ((96+16*c)*(length+2)) hLengthWord
  have hRat : BinarySequentialRationalFrame.price model c length ≤ (256+64*c)*G+5*P := by
    unfold BinarySequentialRationalFrame.price
    have hh := Nat.mul_le_mul_left ((256+64*c)*(length+2)) hLengthWord
    have hr := Nat.mul_le_mul_left 5 hRat1
    dsimp only [G]
    nlinarith only [hh,hr]
  have hScalar : BinarySequentialPayloadCost.scalarBound c count ≤ (12+4*c)*Q+16 := by
    unfold BinarySequentialPayloadCost.scalarBound
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hCountWord) 16
  have hGate : BinarySequentialGameFrame.countGatePrice c count ≤
      (count+1)*((c+2)*Q+1)+(c+2)*Q+1 := by
    unfold BinarySequentialGameFrame.countGatePrice
    exact Nat.add_le_add_right (Nat.add_le_add
      (Nat.mul_le_mul_left (count+1) (Nat.add_le_add_right (Nat.mul_le_mul_left (c+2) hFirstWord) 1))
      (Nat.mul_le_mul_left (c+2) hCountZero)) 1
  have hTable : BinaryReferenceCheckedPreparation.tableBound c count length ≤ (4*c+20)*N*G+1 := by
    have hm := Nat.mul_le_mul (show length+1 ≤ length+2 by omega) hTableWord
    have hh := Nat.mul_le_mul_left ((4*c+20)*N) hm
    unfold BinaryReferenceCheckedPreparation.tableBound
    simpa only [N,G,Nat.mul_assoc] using Nat.add_le_add_right hh 1
  have hHeader :
      256*(c+1)*(binaryWordWidth count+1)*(binaryWordWidth (binaryWordWidth count+2)+1)+
        6*binaryWordWidth count+5 ≤ 256*(c+1)*G+6*(length+1)+5 := by
    have hh := Nat.mul_le_mul_left (256*(c+1)) (Nat.mul_le_mul hHeaderWord hHeaderLog)
    have hw : binaryWordWidth count ≤ length+1 := by omega
    have hp := Nat.mul_le_mul_left 6 hw
    dsimp only [G]
    nlinarith only [hh,hp]
  have hGame : BinarySequentialGameFrame.checkedPrice model c count length ≤
      (96+16*c)*G+(count+3)*((256+64*c)*G+5*P+(12+4*c)*Q+16+9)+16+
        (19*count+23)*P+((count+1)*((c+2)*Q+1)+(c+2)*Q+1)+16 := by
    unfold BinarySequentialGameFrame.checkedPrice BinarySequentialGameFrame.gamePrice
    have hRows := Nat.mul_le_mul_left (count+3) (Nat.add_le_add_right (Nat.add_le_add hRat hScalar) 9)
    have hCheck := Nat.mul_le_mul_left (19*count+23) hRat2
    nlinarith only [hNat,hRows,hCheck,hGate]
  have hAccuracyPrice := Nat.mul_le_mul_left (127+48*c) hAccuracy
  unfold NativePRGRequestPreparation.componentBound bound
  change _ ≤ 1000000*(c+1)*N*(P+G)
  have hCountFactor : count+3 ≤ 3*N := by dsimp [N]; omega
  have hFrame := Nat.mul_le_mul_left ((12+4*c)*(count+3)) hQG
  have hCheap := Nat.mul_le_mul_left ((96+16*c)+256*(c+1)) hGN
  calc
    _ ≤ (96+16*c)*G+(count+3)*((256+64*c)*G+5*P+(12+4*c)*G+16+9)+16+
        (19*count+23)*P+((count+1)*((c+2)*G+1)+(c+2)*G+1)+16+
        ((4*c+20)*N*G+1)+(127+48*c)*length+634+240*c+
        (256*(c+1)*G+6*(length+1)+5) := by
          have hQGate := Nat.mul_le_mul_left ((count+2)*(c+2)) hQG
          nlinarith only [hGame,hTable,hHeader,hAccuracyPrice,hFrame,hQGate]
    _ ≤ _ := by
      have h1 := Nat.mul_le_mul_left ((256+64*c)+(12+4*c)) hCountFactor
      have h2 := Nat.mul_le_mul_right G h1
      have h3 := Nat.mul_le_mul_right P (show 5*(count+3)+(19*count+23) ≤ 38*N by dsimp [N]; omega)
      have h4 := Nat.mul_le_mul_right G (show (count+2)*(c+2) ≤ 2*N*(c+2) by dsimp [N]; nlinarith)
      dsimp only [N] at *
      nlinarith only [h2,h3,h4,hCheap,hOne,hG,hN,hGN]

/-! The remaining source wrapper charges both case tests, copying the
dimension/precision words and six reference fields (including returned
option/existential records). References use a padded input-length source
word; this is not a native object-header or allocator cost. -/

def wrappingWork (primitive : ℕ → ℕ) (length count precision : ℕ) : ℕ :=
  2+binaryWordWidth count+primitive (binaryWordWidth count)+
    binaryWordWidth precision+primitive (binaryWordWidth precision)+6*(length+10)

theorem wrapping_work_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (length count precision : ℕ) (hCount : count ≤ length) (hPrecision : precision ≤ length+6) :
    wrappingWork primitive length count precision ≤ (2*c+10)*(length+10) := by
  have hn := Nat.log2_le_self count
  have hK := Nat.log2_le_self precision
  have hw1 : binaryWordWidth count ≤ length+10 := by unfold binaryWordWidth; omega
  have hw2 : binaryWordWidth precision ≤ length+10 := by unfold binaryWordWidth; omega
  have hp1 := (hPrimitive (binaryWordWidth count)).trans (Nat.mul_le_mul_left c hw1)
  have hp2 := (hPrimitive (binaryWordWidth precision)).trans (Nat.mul_le_mul_left c hw2)
  unfold wrappingWork
  nlinarith only [hw1,hw2,hp1,hp2]

def wrapperWork (primitive : ℕ → ℕ) (frame : List Bool) : ℕ :=
  match NativePRGRequestPreparation.prepare frame with
  | none => 2
  | some prepared => wrappingWork primitive frame.length prepared.1 prepared.2.precision

def execute (model : RationalCostModel) (primitive : ℕ → ℕ) (frame : List Bool) :
    Option (Σ n,NativePRGPreparedSampler.Prepared n) × ℕ :=
  let preparedPrefix := NativePRGRequestPreparation.readPrecisionWork model primitive frame
  match NativePRGRequestPreparation.readWords frame with
  | none => (none,preparedPrefix+2)
  | some parsed =>
      if parsed.2.2 = [] then
        let prepared := NativePRGPreparedSampler.ofInput parsed.1.2 parsed.2.1.precision
        (some ⟨parsed.1.1,prepared⟩,preparedPrefix+
          NativePRGPreparedSampler.headerWork primitive parsed.1.1+
          wrappingWork primitive frame.length parsed.1.1 parsed.2.1.precision)
      else (none,preparedPrefix+2)

theorem execute_data (model : RationalCostModel) (primitive : ℕ → ℕ) (frame : List Bool) :
    (execute model primitive frame).1 = NativePRGRequestPreparation.prepare frame := by
  unfold execute NativePRGRequestPreparation.prepare
  cases NativePRGRequestPreparation.readWords frame with
  | none => rfl
  | some parsed =>
      dsimp only [Option.bind_some]
      split <;> rfl

theorem execute_work (model : RationalCostModel) (primitive : ℕ → ℕ) (frame : List Bool) :
    (execute model primitive frame).2 =
      NativePRGRequestPreparation.componentWork model primitive frame+wrapperWork primitive frame := by
  unfold execute NativePRGRequestPreparation.componentWork wrapperWork NativePRGRequestPreparation.prepare
  cases NativePRGRequestPreparation.readWords frame with
  | none => rfl
  | some parsed =>
      dsimp only [Option.bind_some]
      split <;> rfl

theorem prepared_bounds (frame : List Bool) (prepared : Σ n,NativePRGPreparedSampler.Prepared n)
    (h : NativePRGRequestPreparation.prepare frame = some prepared) :
    prepared.1 ≤ frame.length ∧ prepared.2.precision ≤ frame.length+6 := by
  unfold NativePRGRequestPreparation.prepare at h
  cases hr : NativePRGRequestPreparation.readWords frame with
  | none => rw [hr,Option.bind_none] at h; cases h
  | some parsed =>
      have hOld : RationalPRGBinaryRequest.readWords frame = some parsed := by
        simpa only [NativePRGRequestPreparation.readWords_refines] using hr
      have hb := RationalPRGBinaryRequest.readWords_bounds frame parsed.1 parsed.2.1 parsed.2.2 hOld
      rw [hr,Option.bind_some] at h
      split at h
      · cases Option.some.inj h
        exact ⟨hb.1,hb.2.2⟩
      · cases h

theorem wrapper_work_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w)
    (frame : List Bool) : wrapperWork primitive frame ≤ (2*c+10)*(frame.length+10) := by
  unfold wrapperWork
  cases h : NativePRGRequestPreparation.prepare frame with
  | none => dsimp only; nlinarith
  | some prepared =>
      have hb := prepared_bounds frame prepared h
      exact wrapping_work_bound primitive c hPrimitive frame.length prepared.1 prepared.2.precision hb.1 hb.2

theorem wrapper_le_bound (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c*w) (count : ℕ) (frame : List Bool) :
    wrapperWork primitive frame ≤ bound model c count frame.length := by
  have hw := wrapper_work_bound primitive c hPrimitive frame
  have hQ : 1 ≤ logFactor frame.length := by unfold logFactor; omega
  have hG := Nat.mul_le_mul_left (frame.length+2) hQ
  have hN : 1 ≤ count+1 := by omega
  have hBase : frame.length+2 ≤ (count+1)*(model.rat (width frame.length)+(frame.length+2)*logFactor frame.length) := by
    have hh := Nat.mul_le_mul_left (count+1) (show frame.length+2 ≤
      model.rat (width frame.length)+(frame.length+2)*logFactor frame.length by omega)
    have hn := Nat.mul_le_mul_right (frame.length+2) hN
    omega
  have hAbs := Nat.mul_le_mul_left (64*(c+1)) hBase
  unfold bound
  calc
    _ ≤ 64*(c+1)*(frame.length+2) := by nlinarith only [hw]
    _ ≤ _ := by nlinarith only [hAbs]

theorem encoded_bounds {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput) :
    n ≤ (RationalPRGBinaryRequest.encode i a).length ∧
      (BinaryAccuracyFrame.encode a).length ≤ (RationalPRGBinaryRequest.encode i a).length := by
  have hg := RationalPRGBinaryInput.encode_length i
  simp only [RationalPRGBinaryRequest.encode,List.length_append]
  omega

theorem encoded_contract {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) :
    let frame := RationalPRGBinaryRequest.encode i a
    (execute model primitive frame).1 = some ⟨n,NativePRGPreparedSampler.ofInput i a.precision⟩ ∧
      (execute model primitive frame).2 ≤ 2*bound model c n frame.length := by
  have hb := encoded_bounds i a
  have hc := (NativePRGRequestPreparation.encoded_preparation_contract i a model primitive c hPrimitive).2
  have hp := component_bound model c n (RationalPRGBinaryRequest.encode i a).length
    (BinaryAccuracyFrame.encode a).length hb.1 hb.2
  have hw := wrapper_le_bound model primitive c hPrimitive n (RationalPRGBinaryRequest.encode i a)
  constructor
  · rw [execute_data]
    exact NativePRGRequestPreparation.prepare_encode i a
  · rw [execute_work]
    omega

theorem profile_log_bound (length : ℕ) :
    binaryWordWidth (width length+2)+1 ≤ 13*logFactor length := by
  have hWidth : width length+2 ≤ 2048*(length+2) := by unfold width; omega
  have hLog := (binaryWordWidth_mono hWidth).trans (binaryWordWidth_mul 2048 (length+2))
  have hConst : binaryWordWidth 2048 = 12 := by decide
  rw [hConst] at hLog
  have hSmall := binaryWordWidth_mono (show length+2 ≤ 9*length+13 by omega)
  have hPos := binaryWordWidth_pos (9*length+13)
  unfold logFactor
  omega

/-! The constants and logarithmic degree below belong to the fixed Rat
profile, uniformly for every operand width, rather than to a particular
instance. This states the paper's fast-profile specialization explicitly. -/
theorem bound_at_profile (model : RationalCostModel) (C d : ℕ)
    (hFast : ∀ w, model.rat w ≤ C*(w+1)*(binaryWordWidth (w+2)+1)^d)
    (c count length : ℕ) :
    2*bound model c count length ≤
      2000000*(c+1)*(C*1025*13^d+1)*(count+1)*(length+2)*(logFactor length)^(d+1) := by
  let Q := logFactor length
  have hQ : 0 < Q := by dsimp [Q,logFactor]; omega
  have hPow := Nat.pow_le_pow_left (profile_log_bound length) d
  have hWord : width length+1 ≤ 1025*(length+2) := by unfold width; omega
  have hRat := (hFast (width length)).trans (Nat.mul_le_mul (Nat.mul_le_mul_left C hWord) hPow)
  have hStep : Q^d ≤ Q^(d+1) := Nat.pow_le_pow_right hQ (Nat.le_succ _)
  have hLinear : Q ≤ Q^(d+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hQ (by omega : 1 ≤ d+1)
  have hRate : model.rat (width length) ≤ C*1025*13^d*(length+2)*Q^(d+1) := by
    have hh := Nat.mul_le_mul_left (C*1025*13^d*(length+2)) hStep
    change model.rat (width length) ≤ C*(1025*(length+2))*(13*Q)^d at hRat
    rw [mul_pow] at hRat
    nlinarith only [hRat,hh]
  have hDigits := Nat.mul_le_mul_left (length+2) hLinear
  have hSum : model.rat (width length)+(length+2)*Q ≤
      (C*1025*13^d+1)*(length+2)*Q^(d+1) := by nlinarith only [hRate,hDigits]
  have hTotal := Nat.mul_le_mul_left (2000000*(c+1)*(count+1)) hSum
  unfold bound
  change _ ≤ 2000000*(c+1)*(C*1025*13^d+1)*(count+1)*(length+2)*Q^(d+1)
  nlinarith only [hTotal]

theorem encoded_profile_contract {n : ℕ} (i : RationalPRGOriginalInput n) (a : BinaryAccuracyInput)
    (model : RationalCostModel) (C d : ℕ)
    (hFast : ∀ w, model.rat w ≤ C*(w+1)*(binaryWordWidth (w+2)+1)^d)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c*w) :
    let frame := RationalPRGBinaryRequest.encode i a
    (execute model primitive frame).1 = some ⟨n,NativePRGPreparedSampler.ofInput i a.precision⟩ ∧
      (execute model primitive frame).2 ≤
        2000000*(c+1)*(C*1025*13^d+1)*(n+1)*(frame.length+2)*(logFactor frame.length)^(d+1) := by
  have h := encoded_contract i a model primitive c hPrimitive
  exact ⟨h.1,h.2.trans (bound_at_profile model C d hFast c n _)⟩

end Blotto.PRGPaperPreparationCost
