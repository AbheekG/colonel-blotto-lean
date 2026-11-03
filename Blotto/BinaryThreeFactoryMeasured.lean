import Blotto.BinaryLifetimeArrayExtras
import Blotto.BinaryQuadraticThreeFactoryMeasured
import Blotto.BinaryThreeGeometryMeasured
import Blotto.BinaryUnorderedThreeLifetime

/-! Complete measured three-variable factories include the actual order test,
regime program/comparison, selected regular or exceptional producer, and original
coordinate restoration. Their returned descriptors equal the selected preceding
descriptors. Work/retained-source bounds derive from canonical original fields;
native environment/reference/observer/ownership/allocator realization is separate. -/

namespace Blotto.BinaryThreeFactoryMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryThreeInputCompiler BinarySyntaxUniformWork
set_option autoImplicit false
set_option maxHeartbeats 3500000

set_option cleanup.letToHave false in
def orderedWithExtras (input : Input) : ((BinaryStoredOverlapEnvironment.Segment 3 9 × Trace) × ℕ) × ℕ :=
  let env := BinaryThreeGeometryMeasured.environment input
  let regime := BinaryThreeGeometryMeasured.regimeWithExtras env.1.1
  let compared := BinaryQuadraticExpressionMeasured.compare regime.1.1.1 BinaryRationalOpcode.zero
  if !compared.1.1 then
    let geometry := BinaryThreeGeometryMeasured.geometryWithExtras env.1.1
    let factory := BinaryQuadraticThreeFactoryMeasured.descriptorWithExtras geometry.1.1.1
    (((factory.1.1.1,wrap 32 2 [env.1.2,regime.1.1.2,compared.1.2,geometry.1.1.2,factory.1.1.2]),
      env.2+regime.1.2+compared.2+geometry.1.2+factory.1.2+16),regime.2+geometry.2+factory.2)
  else
    let factory := BinaryThreeReferenceMeasured.exceptional input
    (((factory.1.1,wrap 32 2 [env.1.2,regime.1.1.2,compared.1.2,factory.1.2]),
      env.2+regime.1.2+compared.2+factory.2+16),regime.2)

def ordered (input : Input) : (BinaryStoredOverlapEnvironment.Segment 3 9 × Trace) × ℕ :=
  (orderedWithExtras input).1

theorem orderedWithExtras_compat (input : Input) :
    (orderedWithExtras input).1 = ordered input := rfl

theorem ordered_record (input : Input) :
    ordered input =
  let env := BinaryThreeGeometryMeasured.environment input
  let regime := BinaryThreeGeometryMeasured.regime env.1.1
  let compared := BinaryQuadraticExpressionMeasured.compare regime.1.1 BinaryRationalOpcode.zero
  if !compared.1.1 then
    let geometry := BinaryThreeGeometryMeasured.geometry env.1.1
    let factory := BinaryQuadraticThreeFactoryMeasured.descriptor geometry.1.1
    ((factory.1.1,wrap 32 2 [env.1.2,regime.1.2,compared.1.2,geometry.1.2,factory.1.2]),
      env.2+regime.2+compared.2+geometry.2+factory.2+16)
  else
    let factory := BinaryThreeReferenceMeasured.exceptional input
    ((factory.1.1,wrap 32 2 [env.1.2,regime.1.2,compared.1.2,factory.1.2]),
      env.2+regime.2+compared.2+factory.2+16) := by
  simp only [ordered,orderedWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryThreeGeometryMeasured.regimeWithExtras_compat,BinaryThreeGeometryMeasured.geometryWithExtras_compat,BinaryQuadraticThreeFactoryMeasured.descriptorWithExtras_compat]

  split <;> rename_i h <;> simp only [h,Bool.false_eq_true,ite_true,ite_false]

theorem ordered_data (input : Input) :
    (ordered input).1.1 = (BinaryOrderedThreeLifetime.descriptorWithTrace input).1 := by
  simp only [ordered_record,BinaryOrderedThreeLifetime.descriptorWithTrace,BinaryThreeGeometryMeasured.environment_data,
    BinaryThreeGeometryLifetime.environmentWithTrace,BinaryThreeGeometryMeasured.regime_erases,
    BinaryQuadraticExpressionMeasured.compare_erases,BinaryThreeGeometryMeasured.geometry_data,
    BinaryQuadraticThreeFactoryMeasured.descriptor_data,BinaryThreeReferenceMeasured.exceptional_data]
  split <;> rename_i h <;> simp only [h,Bool.false_eq_true,ite_true,ite_false]

def orderedWork (s : ℕ) : ℕ := 2324+BinaryThreeGeometryMeasured.regimeWork s+
  BinaryQuadraticExpression.uniformPrice (expressionHeightBudget s 2)+BinaryThreeGeometryMeasured.geometryWork s+
  BinaryQuadraticThreeFactoryMeasured.workEnvelope (expressionHeightBudget s 2)+50000+16

def orderedEnvelope (s : ℕ) : ℕ := 1277+BinaryThreeGeometryLifetime.regimeEnvelope s+
  BinaryThreeGeometryLifetime.comparisonEnvelope (2*expressionHeightBudget s 2+1)+BinaryThreeGeometryMeasured.geometryEnvelope s+
  BinaryQuadraticThreeFactoryMeasured.envelope (expressionHeightBudget s 2)+50000+64

theorem geometry_data (input : Input) (hC : input.Canonical) :
    (BinaryThreeGeometryMeasured.geometry input.environment).1.1 = geometryEnvironment input := by
  rw [BinaryThreeGeometryMeasured.geometry_data,
    BinaryThreeGeometryLifetime.geometryWithTrace_erasure input.environment (input_canonical input hC)]
  rfl

theorem comparison_work (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryOrderedThreeFactoryWork.InputHeight input s) :
    (BinaryQuadraticExpressionMeasured.compare (BinaryThreeGeometryMeasured.regime input.environment).1.1
      BinaryRationalOpcode.zero).2 ≤ BinaryQuadraticExpression.uniformPrice (expressionHeightBudget s 2) := by
  rw [BinaryQuadraticExpressionMeasured.compare_work,BinaryThreeGeometryMeasured.regime_erases]
  exact BinaryQuadraticExpression.comparePrice_bound _ _ _
    (by have h := BinaryOrderedThreeLifetimeBound.regime_width input hC s hs hH; omega)
    (by change 1 ≤ _; omega)

theorem comparison_usage (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryOrderedThreeFactoryWork.InputHeight input s) :
    usage (BinaryQuadraticExpressionMeasured.compare (BinaryThreeGeometryMeasured.regime input.environment).1.1
      BinaryRationalOpcode.zero).1.2 ≤ BinaryThreeGeometryLifetime.comparisonEnvelope (2*expressionHeightBudget s 2+1) := by
  rw [BinaryQuadraticExpressionMeasured.compare_erases,BinaryThreeGeometryMeasured.regime_erases]
  exact BinaryThreeGeometryLifetime.comparison_usage _ _ _
    (BinaryOrderedThreeLifetimeBound.regime_width input hC s hs hH) (by change 1 ≤ _; omega)

theorem ordered_work (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryOrderedThreeFactoryWork.InputHeight input s) : (ordered input).2 ≤ orderedWork s := by
  have hEnv := BinaryThreeGeometryMeasured.environment_work input
  have hRegime := BinaryThreeGeometryMeasured.regime_work input.environment (input_canonical input hC) s hs
    (BinaryOrderedThreeFactoryWork.environment_height input s hH)
  have hCompare := comparison_work input hC s hs hH
  have hGeometry := BinaryThreeGeometryMeasured.geometry_work input.environment (input_canonical input hC) s hs
    (BinaryOrderedThreeFactoryWork.environment_height input s hH)
  have hFactory := BinaryQuadraticThreeFactoryMeasured.descriptor_work (geometryEnvironment input) (geometry_canonical input hC)
    (expressionHeightBudget s 2) (hs.trans (expressionHeightBudget_ge_input s 2))
    (BinaryOrderedThreeFactoryWork.geometry_height input hC s hs hH)
  rw [← geometry_data input hC] at hFactory
  have hExceptional := BinaryThreeReferenceMeasured.exceptional_work input
  simp only [ordered_record]
  simp only [BinaryThreeGeometryMeasured.environment_data]
  split <;> unfold orderedWork <;> omega

theorem ordered_usage (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryOrderedThreeFactoryWork.InputHeight input s) : usage (ordered input).1.2 ≤ orderedEnvelope s := by
  let env := BinaryThreeGeometryMeasured.environment input
  let regime := BinaryThreeGeometryMeasured.regime input.environment
  let compared := BinaryQuadraticExpressionMeasured.compare regime.1.1 BinaryRationalOpcode.zero
  let geometry := BinaryThreeGeometryMeasured.geometry input.environment
  let factory := BinaryQuadraticThreeFactoryMeasured.descriptor geometry.1.1
  have hEnv := BinaryThreeGeometryMeasured.environment_usage input
  have hRegime := BinaryThreeGeometryMeasured.regime_usage input.environment (input_canonical input hC) s hs
    (BinaryOrderedThreeFactoryWork.environment_height input s hH)
  have hCompare := comparison_usage input hC s hs hH
  have hGeometry := BinaryThreeGeometryMeasured.geometry_usage input.environment (input_canonical input hC) s hs
    (BinaryOrderedThreeFactoryWork.environment_height input s hH)
  have hFactory := BinaryQuadraticThreeFactoryMeasured.descriptor_usage (geometryEnvironment input) (geometry_canonical input hC)
    (expressionHeightBudget s 2) (hs.trans (expressionHeightBudget_ge_input s 2))
    (BinaryOrderedThreeFactoryWork.geometry_height input hC s hs hH)
  rw [← geometry_data input hC] at hFactory
  have hExceptional := BinaryThreeReferenceMeasured.exceptional_usage input
  change usage env.1.2 ≤ _ at hEnv
  change usage regime.1.2 ≤ _ at hRegime
  change usage compared.1.2 ≤ _ at hCompare
  change usage geometry.1.2 ≤ _ at hGeometry
  change usage factory.1.2 ≤ _ at hFactory
  simp only [ordered_record]
  simp only [BinaryThreeGeometryMeasured.environment_data]
  split
  · have hw := wrap_usage 32 2 [env.1.2,regime.1.2,compared.1.2,geometry.1.2,factory.1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 32 2 [env.1.2,regime.1.2,compared.1.2,geometry.1.2,factory.1.2]) ≤ _
    unfold orderedEnvelope
    omega
  · have hw := wrap_usage 32 2 [env.1.2,regime.1.2,compared.1.2,(BinaryThreeReferenceMeasured.exceptional input).1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 32 2 [env.1.2,regime.1.2,compared.1.2,(BinaryThreeReferenceMeasured.exceptional input).1.2]) ≤ _
    unfold orderedEnvelope
    omega

def restore (order : (Bool × Trace) × ℕ) (child : (BinaryStoredOverlapEnvironment.Segment 3 9 × Trace) × ℕ) :
    (BinaryStoredOverlapEnvironment.Segment 3 9 × Trace) × ℕ :=
  if order.1.1 then
    ((child.1.1,wrap 32 2 [order.1.2,child.1.2]),order.2+child.2+8)
  else
    let restored := BinaryThreeReferenceMeasured.swap child.1.1
    ((restored.1.1,wrap 32 2 [order.1.2,child.1.2,restored.1.2]),order.2+child.2+restored.2+12)

set_option cleanup.letToHave false in
def descriptorWithExtras (input : Input) : ((BinaryStoredOverlapEnvironment.Segment 3 9 × Trace) × ℕ) × ℕ :=
  let order := BinaryQuadraticExpressionMeasured.compare input.a input.d
  let child := orderedWithExtras (if order.1.1 then input else ⟨input.B,input.d,input.a,input.c,input.p⟩)
  (restore order child.1,child.2)

def descriptor (input : Input) : (BinaryStoredOverlapEnvironment.Segment 3 9 × Trace) × ℕ :=
  (descriptorWithExtras input).1

theorem descriptorWithExtras_compat (input : Input) :
    (descriptorWithExtras input).1 = descriptor input := rfl

theorem descriptor_record (input : Input) :
    descriptor input =
  let order := BinaryQuadraticExpressionMeasured.compare input.a input.d
  let child := ordered (if order.1.1 then input else ⟨input.B,input.d,input.a,input.c,input.p⟩)
  restore order child := by
  simp only [descriptor,descriptorWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryThreeGeometryMeasured.regimeWithExtras_compat,BinaryThreeGeometryMeasured.geometryWithExtras_compat,BinaryQuadraticThreeFactoryMeasured.descriptorWithExtras_compat,orderedWithExtras_compat]

theorem descriptor_data (input : Input) :
    (descriptor input).1.1 = (BinaryUnorderedThreeLifetime.descriptorWithTrace input).1 := by
  simp only [descriptor_record,restore,BinaryUnorderedThreeLifetime.descriptorWithTrace,BinaryUnorderedThreeLifetime.restoreWithTrace,
    BinaryQuadraticExpressionMeasured.compare_erases,ordered_data,BinaryThreeReferenceMeasured.swap_data]
  split <;> rfl

def workEnvelope (s : ℕ) : ℕ := BinaryQuadraticExpression.uniformPrice s+orderedWork s+50000+12
def envelope (s : ℕ) : ℕ := BinaryThreeGeometryLifetime.comparisonEnvelope (2*s+1)+orderedEnvelope s+50000+64

theorem restore_bounds (order : (Bool × Trace) × ℕ) (child : (BinaryStoredOverlapEnvironment.Segment 3 9 × Trace) × ℕ)
    (W U H V : ℕ) (hW : order.2 ≤ W) (hU : usage order.1.2 ≤ U)
    (hH : child.2 ≤ H) (hV : usage child.1.2 ≤ V) :
    (restore order child).2 ≤ W+H+50000+12 ∧ usage (restore order child).1.2 ≤ U+V+50000+64 := by
  have hSwapW := BinaryThreeReferenceMeasured.swap_work child.1.1
  have hSwapU := BinaryThreeReferenceMeasured.swap_usage child.1.1
  unfold restore
  split
  · have hw := wrap_usage 32 2 [order.1.2,child.1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change order.2+child.2+8 ≤ _ ∧ usage (wrap 32 2 [order.1.2,child.1.2]) ≤ _
    exact ⟨by omega,by omega⟩
  · have hw := wrap_usage 32 2 [order.1.2,child.1.2,(BinaryThreeReferenceMeasured.swap child.1.1).1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change order.2+child.2+(BinaryThreeReferenceMeasured.swap child.1.1).2+12 ≤ _ ∧
      usage (wrap 32 2 [order.1.2,child.1.2,(BinaryThreeReferenceMeasured.swap child.1.1).1.2]) ≤ _
    exact ⟨by omega,by omega⟩

theorem descriptor_bounds (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryOrderedThreeFactoryWork.InputHeight input s) :
    (descriptor input).2 ≤ workEnvelope s ∧ usage (descriptor input).1.2 ≤ envelope s := by
  let order := BinaryQuadraticExpressionMeasured.compare input.a input.d
  let childInput : Input := if order.1.1 then input else ⟨input.B,input.d,input.a,input.c,input.p⟩
  let child := ordered childInput
  have hChildInput : childInput = BinaryThreeSpecCompiler.ordered input := by
    simp only [childInput,order,BinaryQuadraticExpressionMeasured.compare_data,BinaryThreeSpecCompiler.ordered]
  have hChildC : childInput.Canonical := by rw [hChildInput]; exact BinaryThreeSpecCompiler.ordered_canonical input hC
  have hChildH : BinaryOrderedThreeFactoryWork.InputHeight childInput s := by
    rw [hChildInput]
    exact BinaryUnorderedThreeFactoryWork.ordered_height input s hH
  have hA : width input.a ≤ 2*s+1 := by
    have h := hC.2.1.2.trans (rationalWordWidth_of_height hH.2.1)
    omega
  have hD : width input.d ≤ 2*s+1 := by
    have h := hC.2.2.1.2.trans (rationalWordWidth_of_height hH.2.2.1)
    omega
  have hOrderW : order.2 ≤ BinaryQuadraticExpression.uniformPrice s := by
    rw [BinaryQuadraticExpressionMeasured.compare_work]
    exact BinaryQuadraticExpression.comparePrice_bound _ _ _ (by omega) (by omega)
  have hOrderU : usage order.1.2 ≤ BinaryThreeGeometryLifetime.comparisonEnvelope (2*s+1) := by
    rw [BinaryQuadraticExpressionMeasured.compare_erases]
    exact BinaryThreeGeometryLifetime.comparison_usage _ _ _ hA hD
  have hChildW := ordered_work childInput hChildC s hs hChildH
  have hChildU := ordered_usage childInput hChildC s hs hChildH
  exact restore_bounds order child _ _ _ _ hOrderW hOrderU hChildW hChildU

theorem all_prefix (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryOrderedThreeFactoryWork.InputHeight input s) (borrowed steps : ℕ) :
    retainedHeap borrowed (descriptor input).1.2 steps ≤ borrowed+envelope s ∧
      framePeak ((descriptor input).1.2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (descriptor_bounds input hC s hs hH).2 borrowed steps

end Blotto.BinaryThreeFactoryMeasured
