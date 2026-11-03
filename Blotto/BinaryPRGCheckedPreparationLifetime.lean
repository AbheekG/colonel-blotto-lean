import Blotto.BinaryPRGNumericalPreparationLifetime

/-! Canonical original words execute the ordered promise check once. Only
acceptance produces the retained ratio/length/resource arrays. Returned
certificates are erased; no rational source or accepted-game assumption is
supplied by the caller. Rejection preserves the original PRG promise scope. -/
namespace Blotto.BinaryPRGCheckedPreparationLifetime
open BinaryRationalNormalization BinaryPRGRecognition BinaryPRGPreparation
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage

def prepareCheckedWithTrace {n : ℕ} (input : Input n) (hC : input.Canonical) :
    Option {prepared : Prepared n // prepared.Valid} × Trace :=
  let checked := BinaryPRGPromiseLifetime.checkWithTrace input
  if h : checked.1 = true then
    let prepared := BinaryPRGNumericalPreparationLifetime.prepareWithTrace input
    have hCheck : input.Checks := (checkBool_iff input hC).mp
      ((BinaryPRGPromiseLifetime.checkWithTrace_state input hC).symm.trans h)
    have hValid : prepared.1.Valid := by
      rw [BinaryPRGNumericalPreparationLifetime.prepareWithTrace_state input hC]
      exact prepare_valid input hC hCheck
    (some ⟨prepared.1,hValid⟩,wrap 32 2 [checked.2,prepared.2])
  else (none,wrap 16 2 [checked.2])

def prepareCheckedWithRows {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    Option {prepared : Prepared n // prepared.Valid} × Trace :=
  let checked := BinaryPRGPromiseLifetime.checkRowsWithTrace input rows
  if h : checked.1 = true then
    let prepared := BinaryPRGNumericalPreparationLifetime.prepareWithRows input rows hRows
    have hCheck : input.Checks := (checkBool_iff input hC).mp
      ((BinaryPRGPromiseLifetime.checkRowsWithTrace_state input hC rows hRows).symm.trans h)
    have hValid : prepared.1.Valid := by
      rw [BinaryPRGNumericalPreparationLifetime.prepareWithRows_state input hC rows hRows]
      exact prepare_valid input hC hCheck
    (some ⟨prepared.1,hValid⟩,wrap 32 2 [checked.2,prepared.2])
  else (none,wrap 16 2 [checked.2])

theorem prepareCheckedWithRows_eq {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    prepareCheckedWithRows input hC rows hRows = prepareCheckedWithTrace input hC := by
  subst rows
  simp only [prepareCheckedWithRows,prepareCheckedWithTrace,
    BinaryPRGPromiseLifetime.checkRowsWithTrace_eq,
    BinaryPRGNumericalPreparationLifetime.prepareWithRows_eq]

theorem prepareCheckedWithTrace_state {n : ℕ} (input : Input n) (hC : input.Canonical) :
    (prepareCheckedWithTrace input hC).1 = prepareChecked input hC := by
  unfold prepareCheckedWithTrace prepareChecked
  dsimp only
  by_cases h : checkBool input = true
  · have hNew := (BinaryPRGPromiseLifetime.checkWithTrace_state input hC).trans h
    rw [dite_eq_left hNew,dite_eq_left h]
    apply congrArg some
    apply Subtype.ext
    change (BinaryPRGNumericalPreparationLifetime.prepareWithTrace input).1 = prepare input
    exact BinaryPRGNumericalPreparationLifetime.prepareWithTrace_state input hC
  · have hNew : ¬ (BinaryPRGPromiseLifetime.checkWithTrace input).1 = true :=
      fun hh => h ((BinaryPRGPromiseLifetime.checkWithTrace_state input hC).symm.trans hh)
    rw [dite_eq_right hNew,dite_eq_right h]

theorem prepareCheckedWithRows_state {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    (prepareCheckedWithRows input hC rows hRows).1 = prepareChecked input hC := by
  rw [prepareCheckedWithRows_eq]
  exact prepareCheckedWithTrace_state input hC

theorem prepareCheckedWithTrace_isSome {n : ℕ} (input : Input n) (hC : input.Canonical) :
    (prepareCheckedWithTrace input hC).1.isSome = true ↔ input.Checks := by
  rw [prepareCheckedWithTrace_state]
  exact prepareChecked_isSome input hC

def envelope (n S : ℕ) : ℕ :=
  BinaryPRGPromiseLifetime.envelope n S+BinaryPRGNumericalPreparationLifetime.envelope n S+128

private theorem wrap_two_usage (a b : Trace) :
    usage (wrap 32 2 [a,b]) ≤ usage a + usage b + 38 := by
  have hw := wrap_usage 32 2 [a,b]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  omega

private theorem wrap_one_usage (a : Trace) :
    usage (wrap 16 2 [a]) ≤ usage a + 20 := by
  have hw := wrap_usage 16 2 [a]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  omega

theorem prepareCheckedWithTrace_usage {n : ℕ} (input : Input n) (hC : input.Canonical) :
    usage (prepareCheckedWithTrace input hC).2 ≤ envelope n (BinaryPRGPreparationWork.storedInputWidth input) := by
  have hCheck := BinaryPRGPromiseLifetime.checkWithTrace_usage input hC
  have hPrepare := BinaryPRGNumericalPreparationLifetime.prepareWithTrace_usage input hC
  unfold prepareCheckedWithTrace
  dsimp only
  split
  · have hCost := wrap_two_usage (BinaryPRGPromiseLifetime.checkWithTrace input).2
      (BinaryPRGNumericalPreparationLifetime.prepareWithTrace input).2
    change usage (wrap 32 2 [(BinaryPRGPromiseLifetime.checkWithTrace input).2,
      (BinaryPRGNumericalPreparationLifetime.prepareWithTrace input).2]) ≤
      BinaryPRGPromiseLifetime.envelope n (BinaryPRGPreparationWork.storedInputWidth input) +
      BinaryPRGNumericalPreparationLifetime.envelope n
        (BinaryPRGPreparationWork.storedInputWidth input) + 128
    calc
      _ ≤ usage (BinaryPRGPromiseLifetime.checkWithTrace input).2 +
          usage (BinaryPRGNumericalPreparationLifetime.prepareWithTrace input).2 + 38 := hCost
      _ ≤ BinaryPRGPromiseLifetime.envelope n (BinaryPRGPreparationWork.storedInputWidth input) +
          BinaryPRGNumericalPreparationLifetime.envelope n
            (BinaryPRGPreparationWork.storedInputWidth input) + 38 :=
        Nat.add_le_add_right (Nat.add_le_add hCheck hPrepare) 38
      _ ≤ _ := Nat.add_le_add_left (by decide : 38 ≤ 128) _
  · have hCost := wrap_one_usage (BinaryPRGPromiseLifetime.checkWithTrace input).2
    change usage (wrap 16 2 [(BinaryPRGPromiseLifetime.checkWithTrace input).2]) ≤
      BinaryPRGPromiseLifetime.envelope n (BinaryPRGPreparationWork.storedInputWidth input) +
      BinaryPRGNumericalPreparationLifetime.envelope n
        (BinaryPRGPreparationWork.storedInputWidth input) + 128
    calc
      _ ≤ usage (BinaryPRGPromiseLifetime.checkWithTrace input).2 + 20 := hCost
      _ ≤ BinaryPRGPromiseLifetime.envelope n
          (BinaryPRGPreparationWork.storedInputWidth input) + 20 :=
        Nat.add_le_add_right hCheck 20
      _ ≤ _ := by
        have hExtra : 20 ≤ BinaryPRGNumericalPreparationLifetime.envelope n
            (BinaryPRGPreparationWork.storedInputWidth input) + 128 :=
          (by decide : 20 ≤ 128).trans (Nat.le_add_left 128 _)
        simpa only [Nat.add_assoc] using Nat.add_le_add_left hExtra
          (BinaryPRGPromiseLifetime.envelope n (BinaryPRGPreparationWork.storedInputWidth input))

theorem prepareCheckedWithRows_usage {n : ℕ} (input : Input n) (hC : input.Canonical)
    (rows : List SignedWord) (hRows : rows = List.ofFn input.values.read) :
    usage (prepareCheckedWithRows input hC rows hRows).2 ≤
      envelope n (BinaryPRGPreparationWork.storedInputWidth input) := by
  rw [prepareCheckedWithRows_eq]
  exact prepareCheckedWithTrace_usage input hC

theorem reject_trace {n : ℕ} (input : Input n) (hC : input.Canonical)
    (h : (prepareCheckedWithTrace input hC).1 = none) :
    (prepareCheckedWithTrace input hC).2 = wrap 16 2 [(BinaryPRGPromiseLifetime.checkWithTrace input).2] := by
  unfold prepareCheckedWithTrace at h ⊢
  dsimp only at h ⊢
  split
  · rename_i hYes
    rw [dite_eq_left hYes] at h
    cases h
  · rfl

theorem reject_usage {n : ℕ} (input : Input n) (hC : input.Canonical)
    (h : (prepareCheckedWithTrace input hC).1 = none) : usage (prepareCheckedWithTrace input hC).2 ≤
      BinaryPRGPromiseLifetime.envelope n (BinaryPRGPreparationWork.storedInputWidth input)+64 := by
  rw [reject_trace input hC h]
  have hCheck := BinaryPRGPromiseLifetime.checkWithTrace_usage input hC
  have hw := wrap_usage 16 2 [(BinaryPRGPromiseLifetime.checkWithTrace input).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  omega

theorem all_prefix {n : ℕ} (input : Input n) (hC : input.Canonical) (borrowed steps : ℕ) :
    retainedHeap borrowed (prepareCheckedWithTrace input hC).2 steps ≤ borrowed+envelope n (BinaryPRGPreparationWork.storedInputWidth input) ∧
    framePeak ((prepareCheckedWithTrace input hC).2.take steps) ≤ envelope n (BinaryPRGPreparationWork.storedInputWidth input) :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (prepareCheckedWithTrace_usage input hC) borrowed steps

macro "unfold_checked_preparation_envelope" : tactic => `(tactic|
  simp only [envelope,BinaryPRGPromiseLifetime.envelope,BinaryPRGPromiseLifetime.remainingEnvelope,
    BinaryPRGPromiseLifetime.fieldsEnvelope,BinaryPRGPromiseControlLifetime.comparisonEnvelope,
    BinaryStoredWordSumLifetime.envelope,BinaryPRGNumericalPreparationLifetime.envelope,
    BinaryLifetimeUsage.opcodeEnvelope,BinaryQuadraticLifetime.opcodeBound,BinaryQuadraticLifetime.opcodeFrames])

theorem envelope_mono {n m S T : ℕ} (hN : n ≤ m) (hS : S ≤ T) : envelope n S ≤ envelope m T := by
  have hPromise := BinaryPRGPromiseLifetime.envelope_mono hN hS
  have hNumerical := BinaryPRGNumericalPreparationLifetime.envelope_mono hN hS
  unfold envelope
  exact Nat.add_le_add_right (Nat.add_le_add hPromise hNumerical) 128

end Blotto.BinaryPRGCheckedPreparationLifetime
