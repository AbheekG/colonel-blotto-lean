import Blotto.BinaryNormalizedCoordinate
import Blotto.BinaryLifetimeArrayExtras
import Blotto.BinaryPlannedQuadratic
import Blotto.BinaryNestedReferenceMeasured
import Blotto.BinarySmallUniformPreparationMeasured

/-! Actual measured comparison, minimum and maximum return the ordered nested
input and its order bit. Full preceding data/trace and source-derived prices
are retained; native model realization remains separate. -/
namespace Blotto.BinaryNestedOrderMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false
attribute [local irreducible] BinaryPlannedQuadratic.apply BinaryPlannedQuadratic.applyMeasured
set_option maxHeartbeats 600000

abbrev Input := BinaryNestedParameters.Input

theorem compare_bounds (a b : SignedWord) (hA : CanonicalWord a) (hB : CanonicalWord b) (s : ℕ)
    (ha : RationalHeight (value a) s) (hb : RationalHeight (value b) s) :
    (BinaryQuadraticExpressionMeasured.compare a b).2 ≤ BinaryQuadraticExpression.uniformPrice s ∧
      usage (BinaryQuadraticExpressionMeasured.compare a b).1.2 ≤ BinaryThreeGeometryLifetime.comparisonEnvelope (2*s+1) := by
  have hWA : width a ≤ 2*s+1 := by have h := hA.2.trans (rationalWordWidth_of_height ha); omega
  have hWB : width b ≤ 2*s+1 := by have h := hB.2.trans (rationalWordWidth_of_height hb); omega
  constructor
  · rw [BinaryQuadraticExpressionMeasured.compare_work]
    exact BinaryQuadraticExpression.comparePrice_bound a b s (by omega) (by omega)
  · rw [BinaryQuadraticExpressionMeasured.compare_erases]
    exact BinaryThreeGeometryLifetime.comparison_usage a b (2*s+1) hWA hWB

def collect (input : Input) (compared : (Bool × Trace) × ℕ) (low high : (SignedWord × Trace) × ℕ) :
    ((Input × Bool) × Trace) × ℕ :=
  ((({ input with a := low.1.1,d := high.1.1 },compared.1.1),wrap 32 2 [compared.1.2,low.1.2,high.1.2]),compared.2+low.2+high.2+12)

set_option cleanup.letToHave false in
def orderWithExtras (input : Input) : (((Input × Bool) × Trace) × ℕ) × ℕ :=
  let compared := BinaryQuadraticExpressionMeasured.compare input.a input.d
  let low := BinaryNormalizedCoordinate.opcode .minimum input.a input.d
  let high := BinaryNormalizedCoordinate.opcode .maximum input.a input.d
  (collect input compared low.1 high.1,low.2+high.2)

def order (input : Input) : ((Input × Bool) × Trace) × ℕ :=
  (orderWithExtras input).1

theorem orderWithExtras_compat (input : Input) :
    (orderWithExtras input).1 = order input := rfl

theorem order_record (input : Input) :
    order input =
  let compared := BinaryQuadraticExpressionMeasured.compare input.a input.d
  let low := BinaryPlannedQuadratic.apply .minimum input.a input.d
  let high := BinaryPlannedQuadratic.apply .maximum input.a input.d
  collect input compared low high := by
  simp only [order,orderWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryNormalizedCoordinate.opcode_record]

theorem order_eq (input : Input) : order input = collect input
    (BinaryQuadraticExpressionMeasured.compare input.a input.d)
    (BinaryQuadraticMeasured.apply .minimum input.a input.d) (BinaryQuadraticMeasured.apply .maximum input.a input.d) := by
  simp only [order_record, BinaryPlannedQuadratic.apply_previous]

theorem order_erases (input : Input) : (order input).1 = BinaryNestedOrderLifetime.orderWithTrace input := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,order_record,collect,BinaryNestedOrderLifetime.orderWithTrace,BinaryQuadraticExpressionMeasured.compare_erases,
    BinaryQuadraticMeasured.apply_erases]

def workEnvelope (s : ℕ) : ℕ := BinaryQuadraticExpression.uniformPrice s+2*BinarySmallUniformSplitMeasured.opcodePrice s+12

theorem collect_work (input : Input) (compared : (Bool × Trace) × ℕ) (low high : (SignedWord × Trace) × ℕ)
    (C M : ℕ) (hc : compared.2 ≤ C) (hl : low.2 ≤ M) (hh : high.2 ≤ M) :
    (collect input compared low high).2 ≤ C+2*M+12 := by
  change compared.2+low.2+high.2+12 ≤ _
  omega

theorem order_bounds (input : Input) (hC : input.Canonical) (s : ℕ)
    (hH : BinaryNestedParameterWork.InputHeight input s) :
    (order input).2 ≤ workEnvelope s ∧ usage (order input).1.2 ≤ BinaryNestedOrderLifetime.orderEnvelope s := by
  have hc := compare_bounds input.a input.d hC.2.1 hC.2.2.1 s hH.2.1 hH.2.2.1
  have hl := BinarySmallUniformPreparationMeasured.opcode_bounds .minimum input.a input.d hC.2.1 hC.2.2.1 s hH.2.1 hH.2.2.1
  have hh := BinarySmallUniformPreparationMeasured.opcode_bounds .maximum input.a input.d hC.2.1 hC.2.2.1 s hH.2.1 hH.2.2.1
  constructor
  · have hResult := collect_work input _ _ _ _ _ hc.1 hl.1 hh.1
    rw [order_eq]
    exact hResult
  · rw [order_erases]
    exact BinaryNestedOrderLifetime.orderWithTrace_usage input hC s hH

theorem order_all_prefix (input : Input) (hC : input.Canonical) (s : ℕ)
    (hH : BinaryNestedParameterWork.InputHeight input s) (borrowed steps : ℕ) :
    retainedHeap borrowed (order input).1.2 steps ≤ borrowed+BinaryNestedOrderLifetime.orderEnvelope s ∧
      framePeak ((order input).1.2.take steps) ≤ BinaryNestedOrderLifetime.orderEnvelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (order_bounds input hC s hH).2 borrowed steps

end Blotto.BinaryNestedOrderMeasured
