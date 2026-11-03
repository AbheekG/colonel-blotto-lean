import Blotto.BinaryArrayProjectionPayloadExposure
import Blotto.BinaryPRGRawRulersWork

/-! Successful raw input exposes the exact copied rows and retained ruler
pair together with frame-derived value-field, scalar-operand and Boolean/list
measurement bounds. These three companion metrics are not an actual host
runtime or borrowed-reference price. -/
namespace Blotto.BinaryPRGInputRulerExposureJoin

theorem raw_data (frame : List Bool)
    (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed) :
    (BinaryArrayProjectionPayloadExposure.readWithPayload
      BinaryArrayProjectionPayloadExposure.fieldBits
      parsed.1.2.request.prepared.original.values.data).1 =
        (BinaryArrayProjectionLifetime.readWithTrace
          parsed.1.2.request.prepared.original.values.data).1 ∧
    (BinaryPRGRawRulersWork.rulersWithWork parsed.1.2).1 =
      (parsed.1.2.precisionRuler,parsed.1.2.choiceRuler) := by
  exact ⟨BinaryArrayProjectionPayloadExposure.read_state _ _,
    BinaryPRGRawRulersWork.read_state frame parsed hRead⟩

theorem raw_exposure (frame : List Bool)
    (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed) :
    (BinaryArrayProjectionPayloadExposure.readWithPayload
      BinaryArrayProjectionPayloadExposure.fieldBits
      parsed.1.2.request.prepared.original.values.data).2 +
    (BinaryArrayProjectionScalarExposure.readWithExposure
      parsed.1.2.request.prepared.original.values.data).2 +
    (BinaryPRGRawRulersWork.rulersWithWork parsed.1.2).2 ≤
      3*frame.length+4 +
        (frame.length+1)*(8+3*binaryWordWidth (frame.length+1))+
          1024*(2*frame.length+8) := by
  have hPayload := BinaryArrayProjectionPayloadExposure.raw_fieldBits_bound frame parsed hRead
  have hScalar := BinaryArrayProjectionScalarExposure.raw_values_bound frame parsed hRead
  have hRulers := BinaryPRGRawRulersWork.read_bound frame parsed hRead
  omega

end Blotto.BinaryPRGInputRulerExposureJoin
