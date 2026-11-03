import Blotto.BinaryLifetimeArrayExtras
import Blotto.BinaryOverlapGluingMeasured
import Blotto.BinaryFourGluingParentsMeasured
import Blotto.BinaryFourGluingLifetime

/-! Actual measured parameters and parent descriptors feed the complete
measured 81-slot overlap factory. Original six-field heights and the gluing
case derive source work and retained-prefix bounds. Exact old descriptor data
is preserved; native label/reference/observer/allocator prices remain separate. -/
namespace Blotto.BinaryFourGluingMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryFourParentCompiler
set_option maxHeartbeats 400000

def collect {α : Type} (parents : (α × Trace) × ℕ)
    (child : (BinaryStoredOverlapEnvironment.Segment 4 81 × Trace) × ℕ) :
    (BinaryStoredOverlapEnvironment.Segment 4 81 × Trace) × ℕ :=
  ((child.1.1,wrap 64 4 [parents.1.2,child.1.2]),parents.2+child.2+8)

set_option cleanup.letToHave false in
def descriptorWithExtras (input : BinaryFourParameters.Input) (hC : input.Canonical) : ((BinaryStoredOverlapEnvironment.Segment 4 81 × Trace) × ℕ) × ℕ :=
  let parents := BinaryFourGluingParentsMeasured.runWithExtras input hC
  let child := BinaryOverlapGluingMeasured.descriptorWithExtras
    parents.1.1.1.2.1 parents.1.1.1.2.2 (parents.1.1.1.1.read 1) input.B
  (collect parents.1 child.1,parents.2+child.2)

def descriptor (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (BinaryStoredOverlapEnvironment.Segment 4 81 × Trace) × ℕ :=
  (descriptorWithExtras input hC).1

theorem descriptorWithExtras_compat (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (descriptorWithExtras input hC).1 = descriptor input hC := rfl

theorem descriptor_record (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    descriptor input hC =
  let parents := BinaryFourGluingParentsMeasured.run input hC
  let child := BinaryOverlapGluingMeasured.descriptor
    parents.1.1.2.1 parents.1.1.2.2 (parents.1.1.1.read 1) input.B
  collect parents child := by
  simp only [descriptor,descriptorWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryFourGluingParentsMeasured.runWithExtras_compat,BinaryOverlapGluingMeasured.descriptorWithExtras_compat]

theorem descriptor_eq (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    descriptor input hC = collect (BinaryFourGluingParentsMeasured.run input hC)
      (BinaryOverlapGluingMeasured.descriptor
        (BinaryFourGluingParentsMeasured.run input hC).1.1.2.1
        (BinaryFourGluingParentsMeasured.run input hC).1.1.2.2
        ((BinaryFourGluingParentsMeasured.run input hC).1.1.1.read 1) input.B) := by
  exact descriptor_record input hC

theorem descriptor_data (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (descriptor input hC).1.1 = (BinaryFourGluingLifetime.descriptorWithTrace input hC).1 := by
  simp only [descriptor_record,collect,BinaryFourGluingLifetime.descriptorWithTrace,
    BinaryFourGluingParentsMeasured.run_data,BinaryOverlapGluingMeasured.descriptor_data]

def workEnvelope (s : ℕ) : ℕ := BinaryFourGluingParentsMeasured.workEnvelope s+
  BinaryOverlapGluingMeasured.workEnvelope 81 (expressionHeightBudget s 30)+8

def envelope (s : ℕ) : ℕ :=
  BinaryFourGluingParentsMeasured.envelope s +
    BinaryOverlapGluingMeasured.envelope 81 (expressionHeightBudget s 30) + 80

theorem collect_bounds {α : Type} (parents : (α × Trace) × ℕ)
    (child : (BinaryStoredOverlapEnvironment.Segment 4 81 × Trace) × ℕ)
    (P C H J : ℕ) (hP : parents.2 ≤ P ∧ usage parents.1.2 ≤ H)
    (hC : child.2 ≤ C ∧ usage child.1.2 ≤ J) :
    (collect parents child).2 ≤ P+C+8 ∧ usage (collect parents child).1.2 ≤ H+J+80 := by
  have hw := wrap_usage 64 4 [parents.1.2,child.1.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change parents.2+child.2+8 ≤ _ ∧ usage (wrap 64 4 [parents.1.2,child.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem descriptor_bounds (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (hCase : (1-source.p)*source.ell ≤ source.w) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) :
    (descriptor input hC).2 ≤ workEnvelope s ∧ usage (descriptor input hC).1.2 ≤ envelope s := by
  let parents := BinaryFourGluingParentsMeasured.run input hC
  let child := BinaryOverlapGluingMeasured.descriptor
    parents.1.1.2.1 parents.1.1.2.2 (parents.1.1.1.read 1) input.B
  have hParents := (BinaryFourGluingParentsMeasured.run_data input hC).trans
    (BinaryFourGluingParentsLifetime.runWithTrace_erasure input hC)
  have hFirst : parents.1.1.2.1.Canonical := BinaryFourGluingParentsMeasured.first_canonical input hC
  have hSecond : parents.1.1.2.2.Canonical := BinaryFourGluingParentsMeasured.second_canonical input hC
  have hInterval : CanonicalWord (parents.1.1.1.read 1) :=
    BinaryFourGluingParentsMeasured.interval_canonical input hC
  have hFR : parents.1.1.2.1.Refines (source.overlapData hCase).first := by
    rw [hParents]
    exact firstParent_refines input source hC hR hCase
  have hSR : parents.1.1.2.2.Refines (source.overlapData hCase).second := by
    rw [hParents]
    exact secondParent_refines input source hC hR hCase
  have hD : value (parents.1.1.1.read 1) = (source.overlapData hCase).d := by
    rw [hParents]
    exact BinaryFourParameters.prepare_value input source hC hR 1
  have hB : value input.B = source.B := hR.1
  have hs12 : 2 ≤ expressionHeightBudget s 12 := (by omega : 2 ≤ s).trans (expressionHeightBudget_ge_input s 12)
  have hFHeight := RationalThreeSpecCode.descriptor_height (source.gluingFirstSpec hCase)
    (expressionHeightBudget s 12) hs12 (hH.gluingFirst_environment (by omega) hCase)
  have hSHeight := RationalThreeSpecCode.descriptor_height (source.gluingSecondSpec hCase)
    (expressionHeightBudget s 12) hs12 (hH.gluingSecond_environment (by omega) hCase)
  rw [expressionHeightBudget_comp] at hFHeight hSHeight
  norm_num only [show 12 + 18 = (30 : ℕ) from rfl] at hFHeight hSHeight
  have hDHeight : RationalHeight (source.overlapData hCase).d (expressionHeightBudget s 30) :=
    (hH.scalar (by omega) 1).mono (expressionHeightBudget_mono s (by decide : 12 ≤ 30))
  have hBHeight : RationalHeight source.B (expressionHeightBudget s 30) :=
    hH.1.mono (expressionHeightBudget_ge_input s 30)
  have hEnv : ∀ i j,BinarySyntaxUniformWork.EnvHeight
      (BinaryStoredOverlapEnvironment.environment parents.1.1.2.1 parents.1.1.2.2
        (parents.1.1.1.read 1) input.B i j) (expressionHeightBudget s 30) := by
    intro i j
    exact BinaryStoredOverlapEnvironment.source_environment_height
      parents.1.1.2.1 parents.1.1.2.2 (parents.1.1.1.read 1) input.B
      (source.overlapData hCase) source.B i j hFR hSR hD hB
      (expressionHeightBudget s 30) hFHeight hSHeight hDHeight hBHeight
  have hs30 : 3 ≤ expressionHeightBudget s 30 := hs.trans (expressionHeightBudget_ge_input s 30)
  have hParentUsage := BinaryFourGluingParentsMeasured.run_bounds input source hC hR hCase s hs hH
  have hChild := BinaryOverlapGluingMeasured.descriptor_bounds
    parents.1.1.2.1 parents.1.1.2.2 (parents.1.1.1.read 1) input.B hFirst hSecond hInterval hC.1
    (expressionHeightBudget s 30) hs30 hEnv
  norm_num only at hChild
  change parents.2 ≤ _ ∧ usage parents.1.2 ≤ _ at hParentUsage
  change child.2 ≤ _ ∧ usage child.1.2 ≤ _ at hChild
  have hCollected := collect_bounds parents child _ _ _ _ hParentUsage hChild
  rw [descriptor_eq]
  simpa only [parents,child,workEnvelope,envelope] using hCollected

theorem all_prefix (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (hCase : (1-source.p)*source.ell ≤ source.w) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (descriptor input hC).1.2 steps ≤ borrowed + envelope s ∧
      framePeak ((descriptor input hC).1.2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (descriptor_bounds input source hC hR hCase s hs hH).2 borrowed steps

end Blotto.BinaryFourGluingMeasured
