import Blotto.BooleanSampleCountLifetime
import Blotto.BooleanFreshBitSeedLoop
import Blotto.BinaryPRGFreshRawLifetime

/-! Actual accepted rows and Boolean accuracy rulers produce the seed counter.
The request's natural dimension/precision are used only in proof statements
and trace reservations. No original payload is numerically decoded and no
scheduled natural count is computed by the counter or generation producers.
Array-to-list reference traversal remains the existing native array boundary. -/
namespace Blotto.BinaryPRGSeedCountLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage RationalLottoResourceSystem
set_option maxHeartbeats 3000000

def rulerWithTrace {n : ℕ} (request : BinaryPRGRequest.Request n) : List Bool × Trace :=
  let shifted := BinaryRulerPrecisionLifetime.shiftedWithTrace request.accuracy.denominator (List.replicate 5 false)
  let ruler := BinaryRulerPrecisionLifetime.prepareWithTrace shifted.1 request.accuracy.numerator
  (ruler.1,wrapList 5 32 2 [shifted.2,ruler.2])

theorem ruler_length {n : ℕ} (request : BinaryPRGRequest.Request n) :
    (rulerWithTrace request).1.length = request.precision := by
  simp only [rulerWithTrace,BinaryRulerPrecisionLifetime.prepareWithTrace_state,BinaryRulerPrecision.prepare_length,
    BinaryRulerPrecisionLifetime.shiftedWithTrace_state,BinaryRulerPrecision.shifted_state,List.length_replicate]
  exact request.precision_eq.symm

theorem ruler_usage {n : ℕ} (request : BinaryPRGRequest.Request n) :
    usage (rulerWithTrace request).2 ≤ 2048*(request.accuracy.numerator.width+request.accuracy.denominator.width+8) := by
  let shifted := BinaryRulerPrecisionLifetime.shiftedWithTrace request.accuracy.denominator (List.replicate 5 false)
  have hShift := BinaryRulerPrecisionLifetime.shiftedWithTrace_usage request.accuracy.denominator (List.replicate 5 false)
  have hRuler := BinaryRulerPrecisionLifetime.prepareWithTrace_usage shifted.1 request.accuracy.numerator
  have hWidth : shifted.1.width = request.accuracy.denominator.width+5 := by
    simp only [shifted,BinaryRulerPrecisionLifetime.shiftedWithTrace_state,BinaryRulerPrecision.shifted_state,
      PositiveBinaryWord.width_shifted,List.length_replicate]
  rw [hWidth] at hRuler
  simp only [List.length_replicate] at hShift
  have hw := wrapList_usage 5 32 2 [shifted.2,(BinaryRulerPrecisionLifetime.prepareWithTrace shifted.1 request.accuracy.numerator).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage shifted.2 ≤ _ at hShift
  change usage (rulerWithTrace request).2 ≤ _ at hw
  omega

def prepareWithTrace {n : ℕ} (request : BinaryPRGRequest.Request n) : List Bool × Trace :=
  let rows := request.prepared.original.values.data.toList
  let ruler := rulerWithTrace request
  let counter := BooleanSampleCountLifetime.prepareWithTrace rows ruler.1
  (counter.1,wrapList rows.length 32 2 [ruler.2,counter.2])

theorem prepare_value {n : ℕ} (request : BinaryPRGRequest.Request n) :
    BinaryBigEndian.littleValue (prepareWithTrace request).1 = sampleBitBudget n request.precision := by
  change BinaryCarryCounter.value (BooleanSampleCountLifetime.prepareWithTrace _ _).1 = _
  rw [BooleanSampleCountLifetime.prepare_value,Array.length_toList,request.prepared.original.values.size,ruler_length,sampleBitBudget_eq]
  omega

theorem prepare_width {n : ℕ} (request : BinaryPRGRequest.Request n) :
    (prepareWithTrace request).1.length ≤ binaryWordWidth (sampleBitBudget n request.precision) := by
  have h := BooleanSampleCountLifetime.prepare_width request.prepared.original.values.data.toList (rulerWithTrace request).1
  rw [Array.length_toList,request.prepared.original.values.size,ruler_length] at h
  rw [sampleBitBudget_eq]
  change (prepareWithTrace request).1.length ≤ _ at h
  have he : 3*n+5*request.precision+3000 = 5*request.precision+3*(n+1000) := by omega
  rw [he] at h
  exact h

theorem precision_bound {n : ℕ} (request : BinaryPRGRequest.Request n) :
    request.precision ≤ request.accuracy.denominator.width+5 := by
  rw [request.precision_eq]
  exact (⟨request.accuracy,request.accuracy.precision,rfl⟩ : BinaryAccuracyRulerReadWork.Prepared).precision_bound

theorem prepare_usage {n : ℕ} (request : BinaryPRGRequest.Request n) :
    usage (prepareWithTrace request).2 ≤ 100000*(n+request.accuracy.numerator.width+request.accuracy.denominator.width+32) := by
  have hRuler := ruler_usage request
  have hCounter := BooleanSampleCountLifetime.prepare_usage request.prepared.original.values.data.toList (rulerWithTrace request).1
  rw [Array.length_toList,request.prepared.original.values.size,ruler_length] at hCounter
  have hK := precision_bound request
  change usage (wrapList _ 32 2 [_,_]) ≤ _
  apply (wrapList_usage _ _ _ _).trans
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Array.length_toList,request.prepared.original.values.size]
  omega

theorem read_accuracy_width (frame : List Bool) (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (h : (BinaryPRGAccuracyRulerRequest.read frame).1 = some parsed) :
    parsed.1.2.request.accuracy.numerator.width+parsed.1.2.request.accuracy.denominator.width ≤ frame.length := by
  unfold BinaryPRGAccuracyRulerRequest.read at h
  dsimp only at h
  split at h
  · cases h
  · rename_i game hg
    have hSuffix := BinaryPRGAccuracyRulerRequest.game_suffix_length frame game hg
    split at h
    · cases h
    · obtain ⟨accuracy,ha,hOut⟩ := Option.map_eq_some_iff.mp h
      have hWidth := BinaryAccuracyRulerReadWork.read_widths game.2 accuracy ha
      subst parsed
      change accuracy.1.words.numerator.width+accuracy.1.words.denominator.width ≤ _
      omega

def generateWithTrace {S : Type*} {n : ℕ} (fresh : S → Bool × S) (request : BinaryPRGRequest.Request n) (state : S) :
    (List Bool × S) × Trace :=
  let counter := prepareWithTrace request
  let seed := BooleanFreshBitSeedLoop.generateWithTrace fresh counter.1 state
  (seed.1,wrap 32 2 [counter.2,seed.2])

theorem generate_state {S : Type*} {n : ℕ} (fresh : S → Bool × S) (request : BinaryPRGRequest.Request n) (state : S) :
    (generateWithTrace fresh request state).1 =
      (FreshBitSeedLifetime.generateWithTrace fresh (sampleBitBudget n request.precision) state).1 := by
  simp only [generateWithTrace,BooleanFreshBitSeedLoop.generate_state,prepare_value]

theorem raw_usage {S : Type*} (fresh : S → Bool × S) (frame : List Bool)
    (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed) (state : S) :
    usage (generateWithTrace fresh parsed.1.2.request state).2 ≤ 2000000*(frame.length+400)^2 := by
  have hOld := (BinaryPRGRawRequestLifetime.readWithTrace_state frame).symm.trans hRead
  have hn := BinaryPRGSeedRequestBound.read_dimension_bound frame parsed hOld
  have hAccuracy := read_accuracy_width frame parsed hOld
  have hN := BinaryPRGSeedRequestBound.read_seedCount_bound frame parsed hOld
  have hWidth := prepare_width parsed.1.2.request
  have hLog := BinaryPRGSeedOutputLifetimePolynomial.wordWidth_le (sampleBitBudget parsed.1.1 parsed.1.2.request.precision)
  have hPrepare := prepare_usage parsed.1.2.request
  have hSeed := BooleanFreshBitSeedLoop.generate_usage fresh (prepareWithTrace parsed.1.2.request).1 state
  rw [prepare_value] at hSeed
  unfold BooleanFreshBitSeedLoop.envelope at hSeed
  have hw := wrap_usage 32 2 [(prepareWithTrace parsed.1.2.request).2,
    (BooleanFreshBitSeedLoop.generateWithTrace fresh (prepareWithTrace parsed.1.2.request).1 state).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (generateWithTrace fresh parsed.1.2.request state).2 ≤ _ at hw
  unfold BinaryPRGSeedRequestBound.seedCountBound at hN
  have hProduct : ((prepareWithTrace parsed.1.2.request).1.length+1)*
      (sampleBitBudget parsed.1.1 parsed.1.2.request.precision+1) ≤ (8*frame.length+3027)*(8*frame.length+3026) := by
    apply Nat.mul_le_mul <;> omega
  nlinarith

end Blotto.BinaryPRGSeedCountLifetime
