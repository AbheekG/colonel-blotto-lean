import Blotto.BooleanFreshSeedAmortized
import Blotto.BinaryResourceTraceLength

/-! Event lengths of the actual retained-ruler seed producer. The carry passes
and Boolean fresh-bit loop keep their existing source work and entropy model. -/
namespace Blotto.BinaryGeneratedSeedTraceBounds
open BinarySeedPreparationSpace BinaryPRGRulerSeedMeasured RationalLottoResourceSystem BinaryPRGHeapTraceUsage
open BinaryResourceTraceLength (under_length)
set_option autoImplicit false

theorem prepare_length {n : ℕ} (request : BinaryPRGAccuracyRulerRequest.Request n) :
    (prepare request).1.2.length ≤ 2*(prepare request).2 := by
  have h1 := BinaryWordStoreMeasured.countAt_trace_work request.choiceRuler [] 0
  have h2 := BinaryWordStoreMeasured.countAt_trace_work request.precisionRuler
    (BinaryWordStoreMeasured.count request.choiceRuler []).1.1 0
  have h3 := BinaryWordStoreMeasured.countAt_trace_work request.precisionRuler
    (BinaryWordStoreMeasured.count request.precisionRuler
      (BinaryWordStoreMeasured.count request.choiceRuler []).1.1).1.1 0
  change (BinaryWordStoreMeasured.count request.choiceRuler []).1.2.length ≤
    2*(BinaryWordStoreMeasured.count request.choiceRuler []).2 at h1
  change (BinaryWordStoreMeasured.count request.precisionRuler
    (BinaryWordStoreMeasured.count request.choiceRuler []).1.1).1.2.length ≤
    2*(BinaryWordStoreMeasured.count request.precisionRuler
      (BinaryWordStoreMeasured.count request.choiceRuler []).1.1).2 at h2
  change (BinaryWordStoreMeasured.count request.precisionRuler
    (BinaryWordStoreMeasured.count request.precisionRuler
      (BinaryWordStoreMeasured.count request.choiceRuler []).1.1).1.1).1.2.length ≤
    2*(BinaryWordStoreMeasured.count request.precisionRuler
      (BinaryWordStoreMeasured.count request.precisionRuler
        (BinaryWordStoreMeasured.count request.choiceRuler []).1.1).1.1).2 at h3
  simp only [prepare,wrap,combine,List.map_cons,List.map_nil,List.flatten_cons,
    List.flatten_nil,List.append_nil,List.length_append,List.length_cons,List.length_nil,under_length]
  omega

theorem generate_length {S : Type*} {n : ℕ} (next : S → Bool × S)
    (request : BinaryPRGAccuracyRulerRequest.Request n) (state : S) :
    (generate next request state).1.2.length ≤ 200*(sampleBitBudget n request.request.precision+1) := by
  have hp := prepare_length request
  have hw := prepare_work request
  have hs := BooleanFreshSeedAmortized.generate_trace_linear next (prepare request).1.1 state
  rw [prepare_value] at hs
  have hc := (prepare_width request).trans (BinaryPRGSeedOutputLifetimePolynomial.wordWidth_le _)
  simp only [generate,wrap,combine,List.map_cons,List.map_nil,List.flatten_cons,
    List.flatten_nil,List.append_nil,List.length_append,List.length_cons,List.length_nil,under_length]
  omega

theorem physical_generate_length {S : Type*} (next : S → Bool × S) (frame : List Bool)
    (parsed : BinaryTerminalPhysicalAllowanceCache.Parsed)
    (hRead : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (state : S) :
    (generate next parsed.1.2.logical state).1.2.length ≤ 1000000*(frame.length+1) := by
  have hRef := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_original frame
  rw [hRead,Option.map_some] at hRef
  have hn := BinaryPRGSeedRequestBound.read_seedCount_bound frame
    (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) hRef.symm
  change sampleBitBudget parsed.1.1 parsed.1.2.logical.request.precision ≤
    BinaryPRGSeedRequestBound.seedCountBound frame.length at hn
  unfold BinaryPRGSeedRequestBound.seedCountBound at hn
  have ht := generate_length next parsed.1.2.logical state
  omega

end Blotto.BinaryGeneratedSeedTraceBounds
