import Blotto.BinaryAccuracyRulerReadWork
import Blotto.BinaryPRGStoredDimensionRequest
import Blotto.BinaryPRGStoredDimensionFrame
import Blotto.BinaryPRGHeaderFrame
import Blotto.BinaryPRGOutputRun

/-! The full raw request joins native stored-dimension parsing with reached
measured positive accuracy words and one retained Boolean-ruler precision.
Exact original fields/output/rejection and hard-budget scopes remain. Complete
recorded frame/promise/numerical/accuracy cell prices derive from incoming
length; scalar/seed/controller/backend/physical/whole-space work is separate. -/

namespace Blotto.BinaryPRGAccuracyRulerRequest
open BinaryRationalNormalization BinaryPRGPreparation

structure Request (n : ℕ) where
  request : BinaryPRGRequest.Request n
  header : BinaryPRGHeaderFrame.Header n
  precisionRuler : List Bool := List.replicate request.precision false
  choiceRuler : List Bool := List.replicate (RationalLottoResourceSystem.coinBitBudget n request.precision) false
  precisionRuler_correct : precisionRuler = List.replicate request.precision false := by rfl
  choiceRuler_correct : choiceRuler = List.replicate (RationalLottoResourceSystem.coinBitBudget n request.precision) false := by rfl

theorem Request.precisionRuler_length {n : ℕ} (prepared : Request n) :
    prepared.precisionRuler.length = prepared.request.precision := by
  rw [prepared.precisionRuler_correct,List.length_replicate]

theorem Request.choiceRuler_length {n : ℕ} (prepared : Request n) :
    prepared.choiceRuler.length = RationalLottoResourceSystem.coinBitBudget n prepared.request.precision := by
  rw [prepared.choiceRuler_correct,List.length_replicate]

@[ext] theorem Request.ext {n : ℕ} {first second : Request n}
    (hr : first.request = second.request) (hh : first.header = second.header) : first = second := by
  cases first with
  | mk r h p c hp hc =>
    cases second with
    | mk r' h' p' c' hp' hc' =>
      dsimp only at hr hh
      subst r'
      subst h'
      have hP := hp.trans hp'.symm
      have hC := hc.trans hc'.symm
      cases hP
      cases hC
      rfl

structure Ledger where
  frame : BinaryPRGStoredDimensionFrame.Ledger
  preparation : BinaryPRGMeasuredPreparation.Ledger
  accuracy : ℕ
  deriving Repr, DecidableEq

def Ledger.recorded (ledger : Ledger) : ℕ := ledger.frame.recorded + ledger.preparation.recorded + ledger.accuracy

def assemble {n : ℕ} (checked : {prepared : Prepared n // prepared.Valid})
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) (header : BinaryPRGHeaderFrame.Header n) : Request n :=
  { request := ⟨checked.val,checked.property,accuracy.words,accuracy.precision,accuracy.correct⟩
    header := header }

theorem assemble_state {n : ℕ} (checked : {prepared : Prepared n // prepared.Valid})
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) (header : BinaryPRGHeaderFrame.Header n) :
    (assemble checked accuracy header).request =
      ⟨checked.val,checked.property,accuracy.words,accuracy.words.precision,rfl⟩ := by
  rcases accuracy with ⟨words,precision,hp⟩
  subst precision
  rfl

def read (bits : List Bool) : Option ((Σ n, Request n) × List Bool) × Ledger :=
  let game := BinaryPRGStoredDimensionFrame.read bits
  match game.1 with
  | none => (none,⟨game.2,⟨0,0⟩,0⟩)
  | some parsed =>
      let prepared := BinaryPRGMeasuredPreparation.prepareChecked parsed.1.2.game.input parsed.1.2.game.canonical
      match prepared.1 with
      | none => (none,⟨game.2,prepared.2,0⟩)
      | some checked =>
          let accuracy := BinaryAccuracyRulerReadWork.read parsed.2
          let result := accuracy.1.map (fun selected =>
            (⟨parsed.1.1,assemble checked selected.1 parsed.1.2.header⟩,selected.2))
          (result,⟨game.2,prepared.2,accuracy.2⟩)

def forget (parsed : (Σ n, Request n) × List Bool) : (Σ n, BinaryPRGRequest.Request n) × List Bool :=
  (⟨parsed.1.1,parsed.1.2.request⟩,parsed.2)

theorem read_state_prior (bits : List Bool) : (read bits).1.map forget =
    (BinaryPRGStoredDimensionRequest.read bits).1.map BinaryPRGStoredDimensionRequest.forget := by
  unfold read BinaryPRGStoredDimensionRequest.read
  dsimp only
  cases hg : (BinaryPRGStoredDimensionFrame.read bits).1 with
  | none => rfl
  | some parsed =>
      dsimp only
      cases hp : (BinaryPRGMeasuredPreparation.prepareChecked parsed.1.2.game.input parsed.1.2.game.canonical).1 with
      | none => rfl
      | some checked =>
          simp only [Option.bind_some]
          rw [← BinaryAccuracyRulerReadWork.read_state parsed.2]
          simp only [Option.map_map,Function.comp_def,forget,BinaryPRGStoredDimensionRequest.forget,
            BinaryAccuracyRulerReadWork.forget,assemble_state]

theorem read_state (bits : List Bool) : (read bits).1.map forget = BinaryPRGRequest.read bits :=
  (read_state_prior bits).trans (BinaryPRGStoredDimensionRequest.read_state bits)

theorem read_ledger_base (bits : List Bool) : (read bits).2.frame.recorded + (read bits).2.preparation.recorded =
    (BinaryPRGStoredDimensionRequest.read bits).2.recorded := by
  unfold read BinaryPRGStoredDimensionRequest.read
  dsimp only
  cases hg : (BinaryPRGStoredDimensionFrame.read bits).1 with
  | none => rfl
  | some parsed =>
      dsimp only
      cases hp : (BinaryPRGMeasuredPreparation.prepareChecked parsed.1.2.game.input parsed.1.2.game.canonical).1 <;> rfl

theorem game_suffix_length (bits : List Bool) (parsed : (Σ n, BinaryPRGHeaderFrame.Parsed n) × List Bool)
    (h : (BinaryPRGStoredDimensionFrame.read bits).1 = some parsed) : parsed.2.length ≤ bits.length := by
  have hOld : (BinaryPRGNormalizedFrameWork.read bits).1 = some parsed :=
    (BinaryPRGNormalizedFrameWork.read_state bits).trans ((BinaryPRGStoredDimensionFrame.read_state bits).symm.trans h)
  have hw := BinaryDecodedInputLength.parsed_widths_consumed bits parsed hOld
  have hp := (BinaryPRGPreparationWork.original_widths parsed.1.2.game.input).2.2.2
  omega

theorem read_accuracy_bound (bits : List Bool) : (read bits).2.accuracy ≤ BinaryAccuracyRulerReadWork.bound bits.length := by
  unfold read
  dsimp only
  split
  · exact Nat.zero_le _
  · rename_i parsed hg
    split
    · exact Nat.zero_le _
    · change (BinaryAccuracyRulerReadWork.read parsed.2).2 ≤ _
      exact (BinaryAccuracyRulerReadWork.read_bound parsed.2).trans
        (BinaryAccuracyRulerReadWork.bound_mono (game_suffix_length bits parsed hg))

def output {n : ℕ} (prepared : Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n prepared.request.precision) → Bool) : List Bool × BinaryPRGOutputRun.Ledger :=
  let row := BinaryPRGOutputRun.originalSample prepared.request rich bits
  let frame := prepared.header.bytes ++ BinaryStoredRowFrame.words (List.ofFn row.1.read)
  let visits := BinaryStoredRowFrameWork.wordsVisits (List.ofFn row.1.read) + 2 * n + prepared.header.bytes.length
  (frame,{row.2 with coordinateFraming := visits})

theorem output_state {n : ℕ} (prepared : Request n) (rich : Bool)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n prepared.request.precision) → Bool) :
    output prepared rich bits = BinaryPRGOutputRun.output prepared.request rich bits := by
  unfold output BinaryPRGOutputRun.output BinaryStoredRowFrame.row BinaryStoredRowFrameWork.rowCoordinateVisits
  simp only [prepared.header.correct]

def run (rich : Bool) (request seed : List Bool) : Option (List Bool × BinaryPRGOutputRun.Ledger) × Ledger :=
  let decoded := read request
  let result := decoded.1.bind (fun parsed =>
    if parsed.2 = [] then
      (RationalPRGBinaryRequest.seedTable (RationalLottoResourceSystem.sampleBitBudget parsed.1.1 parsed.1.2.request.precision) seed).map
        (fun table => output parsed.1.2 rich table.read)
    else none)
  (result,decoded.2)

theorem run_state (rich : Bool) (request seed : List Bool) :
    (run rich request seed).1 = BinaryPRGOutputRun.run rich request seed := by
  have hr := read_state request
  cases h : (read request).1 with
  | none =>
      rw [h,Option.map_none] at hr
      simp only [run,h,BinaryPRGOutputRun.run,← hr,Option.bind_none]
  | some parsed =>
      rw [h,Option.map_some] at hr
      simp only [run,h,BinaryPRGOutputRun.run,← hr,Option.bind_some,forget]
      split
      · simp only [output_state]
      · rfl

theorem run_prefix (rich : Bool) (request seed : List Bool) : (run rich request seed).2 = (read request).2 := rfl

theorem run_returned_budget (rich : Bool) (request seed : List Bool) (returned : List Bool × BinaryPRGOutputRun.Ledger)
    (h : (run rich request seed).1 = some returned) :
    ∃ parsed : Σ n, BinaryPRGRequest.Request n,
      RationalPRGBinaryRequest.readWords request = some ((⟨parsed.1,parsed.2.source⟩ : Σ n,RationalPRGOriginalInput n),parsed.2.accuracy,[]) ∧
      RationalPRGBinaryRequest.ReturnedBudget parsed.1 (if rich then parsed.2.source.a else parsed.2.source.b) returned.1 := by
  rw [run_state] at h
  exact BinaryPRGOutputRun.run_returned_budget rich request seed returned h

theorem run_output_recorded_bound (rich : Bool) (request seed : List Bool) (returned : List Bool × BinaryPRGOutputRun.Ledger)
    (h : (run rich request seed).1 = some returned) :
    ∃ parsed : Σ n, BinaryPRGRequest.Request n,
      BinaryPRGRequest.read request = some (parsed,[]) ∧ returned.2.recorded ≤ BinaryPRGOutputRun.bound parsed.2 := by
  rw [run_state] at h
  exact BinaryPRGOutputRun.run_recorded_bound rich request seed returned h

theorem read_precision_bound (bits : List Bool) (parsed : (Σ n, Request n) × List Bool)
    (h : (read bits).1 = some parsed) : parsed.1.2.request.precision ≤ bits.length + 5 := by
  unfold read at h
  dsimp only at h
  split at h
  · cases h
  · rename_i game hg
    have hs := game_suffix_length bits game hg
    split at h
    · cases h
    · obtain ⟨accuracy,ha,hOut⟩ := Option.map_eq_some_iff.mp h
      have hp := BinaryAccuracyRulerReadWork.read_precision_bound game.2 accuracy ha
      subst parsed
      exact hp.trans (Nat.add_le_add_right hs 5)

def inputBound (length : ℕ) : ℕ := BinaryPRGStoredDimensionRequest.inputBound length + BinaryAccuracyRulerReadWork.bound length

theorem read_input_bound (bits : List Bool) : (read bits).2.recorded ≤ inputBound bits.length := by
  change (read bits).2.frame.recorded + (read bits).2.preparation.recorded + (read bits).2.accuracy ≤ _
  rw [read_ledger_base]
  exact Nat.add_le_add (BinaryPRGStoredDimensionRequest.read_input_bound bits) (read_accuracy_bound bits)

def polynomialBound (length : ℕ) : ℕ := 8614755108 * (length + 1) ^ 4

theorem inputBound_polynomial (length : ℕ) : inputBound length ≤ polynomialBound length := by
  have hp := Nat.pow_le_pow_right (by omega : 0 < length + 1) (by decide : 1 ≤ 4)
  simp only [pow_one] at hp
  have ha : BinaryAccuracyRulerReadWork.bound length ≤ 70 * (length + 1) ^ 4 := by
    unfold BinaryAccuracyRulerReadWork.bound
    nlinarith
  unfold inputBound polynomialBound
  calc
    _ ≤ BinaryPRGStoredDimensionRequest.polynomialBound length + 70 * (length + 1) ^ 4 :=
      Nat.add_le_add (BinaryPRGStoredDimensionRequest.inputBound_polynomial length) ha
    _ = _ := by unfold BinaryPRGStoredDimensionRequest.polynomialBound; ring

theorem read_polynomial (bits : List Bool) : (read bits).2.recorded ≤ polynomialBound bits.length :=
  (read_input_bound bits).trans (inputBound_polynomial bits.length)

theorem run_input_bound (rich : Bool) (request seed : List Bool) :
    (run rich request seed).2.recorded ≤ inputBound request.length := read_input_bound request

theorem run_polynomial (rich : Bool) (request seed : List Bool) :
    (run rich request seed).2.recorded ≤ polynomialBound request.length := read_polynomial request


end Blotto.BinaryPRGAccuracyRulerRequest
