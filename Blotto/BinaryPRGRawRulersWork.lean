import Blotto.BinaryPRGRequestRulersWork
import Blotto.BinaryPRGSeedCountLifetime
import Blotto.PRGNativeArrayControl
import Blotto.BinaryArrayProjectionScalarExposure

/-! A measured counterpart for the pair of rulers retained by a successful
complete raw request. Its work bound is derived from that request's actual
incoming frame, but this companion still projects the stored native array;
the selected parser now reuses its retained row list. Native reference-bit,
scalar-operation and counter-arithmetic prices remain separate. -/
namespace Blotto.BinaryPRGRawRulersWork

def selectedRulersWithWork {n : ℕ} (checked : BinaryPRGHeaderFrame.Checked n)
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) : (List Bool × List Bool) × ℕ :=
  BinaryPRGRequestRulersWork.rulersWithRowsWork checked.rows accuracy

theorem selectedRulers_state {n : ℕ} (checked : BinaryPRGHeaderFrame.Checked n)
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) :
    (selectedRulersWithWork checked accuracy).1 =
      ((BinaryPRGRequestRulers.assembleWithRows checked.prepared accuracy checked.header
        checked.rows checked.rows_length).1.precisionRuler,
       (BinaryPRGRequestRulers.assembleWithRows checked.prepared accuracy checked.header
        checked.rows checked.rows_length).1.choiceRuler) :=
  BinaryPRGRequestRulersWork.rulersWithRows_state _ _ _ _ _

theorem selectedRulers_bound {n : ℕ} (checked : BinaryPRGHeaderFrame.Checked n)
    (accuracy : BinaryAccuracyRulerReadWork.Prepared) :
    (selectedRulersWithWork checked accuracy).2 ≤
      512*(n+accuracy.words.numerator.width+accuracy.words.denominator.width+8) :=
  BinaryPRGRequestRulersWork.rulersWithRows_work checked.rows checked.rows_length accuracy

theorem selectedRulers_frame_bound (frame : List Bool)
    (parsed : (Σ n,BinaryPRGHeaderFrame.Checked n) × List Bool)
    (selected : BinaryAccuracyRulerReadWork.Prepared × List Bool)
    (hGame : (BinaryPRGCheckedGameLifetime.readWithTrace frame).1 = some parsed)
    (hAccuracy : (BinaryAccuracyLifetime.readWithTrace parsed.2).1 = some selected) :
    (selectedRulersWithWork parsed.1.2 selected.1).2 ≤ 512*(2*frame.length+8) := by
  have hn := BinaryPRGRawRequestLifetime.checked_dimension_bound frame parsed hGame
  have hSuffix := BinaryPRGRawRequestLifetime.checked_suffix_length frame parsed hGame
  have hw := BinaryAccuracyRulerReadWork.read_widths parsed.2 selected
    ((BinaryAccuracyLifetime.readWithTrace_state parsed.2).symm.trans hAccuracy)
  have hr := selectedRulers_bound parsed.1.2 selected.1
  omega

theorem selectedRulers_raw_join (frame : List Bool)
    (parsed : (Σ n,BinaryPRGHeaderFrame.Checked n) × List Bool)
    (selected : BinaryAccuracyRulerReadWork.Prepared × List Bool)
    (hGame : (BinaryPRGCheckedGameLifetime.readWithTrace frame).1 = some parsed)
    (hAccuracy : (BinaryAccuracyLifetime.readWithTrace parsed.2).1 = some selected) :
    (BinaryPRGRawRequestLifetime.readWithTrace frame).1 =
      some (⟨parsed.1.1,(BinaryPRGRequestRulers.assembleWithRows parsed.1.2.prepared
        selected.1 parsed.1.2.header parsed.1.2.rows parsed.1.2.rows_length).1⟩,selected.2) ∧
    (selectedRulersWithWork parsed.1.2 selected.1).1 =
      ((BinaryPRGRequestRulers.assembleWithRows parsed.1.2.prepared selected.1
        parsed.1.2.header parsed.1.2.rows parsed.1.2.rows_length).1.precisionRuler,
       (BinaryPRGRequestRulers.assembleWithRows parsed.1.2.prepared selected.1
        parsed.1.2.header parsed.1.2.rows parsed.1.2.rows_length).1.choiceRuler) ∧
    (selectedRulersWithWork parsed.1.2 selected.1).2 ≤ 512*(2*frame.length+8) := by
  refine ⟨?_,selectedRulers_state _ _,selectedRulers_frame_bound frame parsed selected hGame hAccuracy⟩
  simp only [BinaryPRGRawRequestLifetime.readWithTrace,hGame,hAccuracy]

def rulersWithWork {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) :
    (List Bool × List Bool) × ℕ :=
  BinaryPRGRequestRulersWork.rulersWithWork
    ⟨prepared.request.prepared,prepared.request.valid⟩
    ⟨prepared.request.accuracy,prepared.request.precision,prepared.request.precision_eq⟩

theorem rulers_state {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) :
    (rulersWithWork prepared).1 = (prepared.precisionRuler,prepared.choiceRuler) := by
  have hAssemble :
      (BinaryPRGRequestRulers.assembleWithTrace
        ⟨prepared.request.prepared,prepared.request.valid⟩
        ⟨prepared.request.accuracy,prepared.request.precision,prepared.request.precision_eq⟩
        prepared.header).1 = prepared := by
    rw [BinaryPRGRequestRulers.assemble_state]
    apply BinaryPRGAccuracyRulerRequest.Request.ext <;> rfl
  rw [rulersWithWork,BinaryPRGRequestRulersWork.rulers_state,hAssemble]

theorem rulers_bound {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) :
    (rulersWithWork prepared).2 ≤
      1024*(n+prepared.request.accuracy.numerator.width+
        prepared.request.accuracy.denominator.width+8) :=
  BinaryPRGRequestRulersWork.rulers_work _ _

theorem read_bound (frame : List Bool)
    (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed) :
    (rulersWithWork parsed.1.2).2 ≤ 1024*(2*frame.length+8) := by
  have hn := PRGNativeArrayControl.dimension_bound frame parsed hRead
  have hOld := (BinaryPRGRawRequestLifetime.readWithTrace_state frame).symm.trans hRead
  have hw := BinaryPRGSeedCountLifetime.read_accuracy_width frame parsed hOld
  exact (rulers_bound parsed.1.2).trans (by omega)

theorem read_state (frame : List Bool)
    (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (_hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed) :
    (rulersWithWork parsed.1.2).1 =
      (parsed.1.2.precisionRuler,parsed.1.2.choiceRuler) := rulers_state _

theorem read_joint_exposure (frame : List Bool)
    (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (hRead : (BinaryPRGRawRequestLifetime.readWithTrace frame).1 = some parsed) :
    (BinaryArrayProjectionScalarExposure.readWithExposure
      parsed.1.2.request.prepared.original.values.data).2 +
      (rulersWithWork parsed.1.2).2 ≤
        (frame.length+1)*(8+3*binaryWordWidth (frame.length+1))+
          1024*(2*frame.length+8) := by
  have hScalar := BinaryArrayProjectionScalarExposure.raw_values_bound frame parsed hRead
  have hRulers := read_bound frame parsed hRead
  omega

end Blotto.BinaryPRGRawRulersWork
