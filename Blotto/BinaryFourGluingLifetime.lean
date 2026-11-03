import Blotto.BinaryOverlapGluingLifetime

/-! The two actually produced three-variable parent tables feed one actual
81-slot overlap descriptor. Original six-field heights and the gluing guard
derive all selected syntax and array reservations; no parent or slot price is
supplied by the caller. -/
namespace Blotto.BinaryFourGluingLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryFourParentCompiler
set_option maxHeartbeats 2000000

def descriptorWithTrace (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    BinaryStoredOverlapEnvironment.Segment 4 81 × Trace :=
  let parents := BinaryFourGluingParentsLifetime.runWithTrace input hC
  let child := BinaryOverlapGluingLifetime.descriptorWithTrace
    parents.1.2.1 parents.1.2.2 (parents.1.1.read 1) input.B
  (child.1,wrap 64 4 [parents.2,child.2])

theorem data_projection (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (descriptorWithTrace input hC).1 =
      (BinaryOverlapGluingLifetime.descriptorWithTrace
        (BinaryFourGluingParentsLifetime.runWithTrace input hC).1.2.1
        (BinaryFourGluingParentsLifetime.runWithTrace input hC).1.2.2
        ((BinaryFourGluingParentsLifetime.runWithTrace input hC).1.1.read 1) input.B).1 := by
  simp only [descriptorWithTrace]

theorem descriptorWithTrace_erasure (input : BinaryFourParameters.Input) (hC : input.Canonical) :
    (descriptorWithTrace input hC).1 = BinaryFourParentCompiler.descriptor input := by
  let parents := BinaryFourGluingParentsLifetime.runWithTrace input hC
  have hFirst : parents.1.2.1.Canonical := BinaryFourGluingParentsLifetime.first_canonical input hC
  have hSecond : parents.1.2.2.Canonical := BinaryFourGluingParentsLifetime.second_canonical input hC
  have hInterval : CanonicalWord (parents.1.1.read 1) :=
    BinaryFourGluingParentsLifetime.interval_canonical input hC
  have hChild := BinaryOverlapGluingLifetime.descriptorWithTrace_erasure
    parents.1.2.1 parents.1.2.2 (parents.1.1.read 1) input.B hFirst hSecond hInterval hC.1
  have hParents := BinaryFourGluingParentsLifetime.runWithTrace_erasure input hC
  have hParam : parents.1.1 = BinaryFourParameters.prepare input :=
    congrArg (fun x => x.1) hParents
  have hF : parents.1.2.1 = firstParent input (BinaryFourParameters.prepare input) :=
    congrArg (fun x => x.2.1) hParents
  have hS : parents.1.2.2 = secondParent input (BinaryFourParameters.prepare input) :=
    congrArg (fun x => x.2.2) hParents
  calc
    _ = (BinaryOverlapGluingLifetime.descriptorWithTrace
          parents.1.2.1 parents.1.2.2 (parents.1.1.read 1) input.B).1 := by
          simpa only [parents] using data_projection input hC
    _ = BinaryStoredOverlapEnvironment.compileDescriptor
          parents.1.2.1 parents.1.2.2 (parents.1.1.read 1) input.B := hChild
    _ = BinaryFourParentCompiler.descriptor input := by
          simp only [BinaryFourParentCompiler.descriptor, hF, hS, hParam]

def envelope (s : ℕ) : ℕ :=
  BinaryFourGluingParentsLifetime.envelope s +
    BinaryOverlapGluingLifetime.descriptorEnvelope 81 (expressionHeightBudget s 30) + 80

theorem descriptorWithTrace_usage (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (hCase : (1-source.p)*source.ell ≤ source.w) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s) :
    usage (descriptorWithTrace input hC).2 ≤ envelope s := by
  let parents := BinaryFourGluingParentsLifetime.runWithTrace input hC
  let child := BinaryOverlapGluingLifetime.descriptorWithTrace
    parents.1.2.1 parents.1.2.2 (parents.1.1.read 1) input.B
  have hParents := BinaryFourGluingParentsLifetime.runWithTrace_erasure input hC
  have hFirst : parents.1.2.1.Canonical := BinaryFourGluingParentsLifetime.first_canonical input hC
  have hSecond : parents.1.2.2.Canonical := BinaryFourGluingParentsLifetime.second_canonical input hC
  have hInterval : CanonicalWord (parents.1.1.read 1) :=
    BinaryFourGluingParentsLifetime.interval_canonical input hC
  have hFR : parents.1.2.1.Refines (source.overlapData hCase).first := by
    rw [hParents]
    exact firstParent_refines input source hC hR hCase
  have hSR : parents.1.2.2.Refines (source.overlapData hCase).second := by
    rw [hParents]
    exact secondParent_refines input source hC hR hCase
  have hD : value (parents.1.1.read 1) = (source.overlapData hCase).d := by
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
      (BinaryStoredOverlapEnvironment.environment parents.1.2.1 parents.1.2.2
        (parents.1.1.read 1) input.B i j) (expressionHeightBudget s 30) := by
    intro i j
    exact BinaryStoredOverlapEnvironment.source_environment_height
      parents.1.2.1 parents.1.2.2 (parents.1.1.read 1) input.B
      (source.overlapData hCase) source.B i j hFR hSR hD hB
      (expressionHeightBudget s 30) hFHeight hSHeight hDHeight hBHeight
  have hs30 : 3 ≤ expressionHeightBudget s 30 := hs.trans (expressionHeightBudget_ge_input s 30)
  have hParentUsage := BinaryFourGluingParentsLifetime.runWithTrace_usage input source hC hR hCase s hs hH
  have hChild := BinaryOverlapGluingLifetime.descriptorWithTrace_usage
    parents.1.2.1 parents.1.2.2 (parents.1.1.read 1) input.B hFirst hSecond hInterval hC.1
    (expressionHeightBudget s 30) hs30 hEnv
  norm_num only at hChild
  change usage parents.2 ≤ _ at hParentUsage
  change usage child.2 ≤ _ at hChild
  have hw := wrap_usage 64 4 [parents.2,child.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 64 4 [parents.2,child.2]) ≤ _
  unfold envelope
  omega

theorem all_prefix (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source)
    (hCase : (1-source.p)*source.ell ≤ source.w) (s : ℕ) (hs : 3 ≤ s) (hH : source.FieldsHeight s)
    (borrowed steps : ℕ) :
    retainedHeap borrowed (descriptorWithTrace input hC).2 steps ≤ borrowed + envelope s ∧
      framePeak ((descriptorWithTrace input hC).2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (descriptorWithTrace_usage input source hC hR hCase s hs hH) borrowed steps

end Blotto.BinaryFourGluingLifetime
