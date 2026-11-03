import Blotto.BinaryReflectedPreparationArithmeticEntryWork
import Blotto.BinaryNestedControlMeasured

/-! Branch-sensitive entry visits for the complete nested control prefix.
Only the reached boundary factory, ordered parameters and regime guards count. -/
namespace Blotto.BinaryNestedControlArithmeticEntryWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryExpressionArithmeticEntryWork (tableCost build_bound quadratic_bound comparison_bound)
open BinaryThreeFactoryArithmeticEntryWork (compiledCost compiled_bound descriptor descriptor_bound)
set_option autoImplicit false
set_option maxHeartbeats 5000000
abbrev Input := BinaryNestedParameters.Input

def programs (n : ℕ) (code : Fin n → BinaryExpressionCompiler.Syntax 7) (input : Input) (x : SignedWord) : ℕ :=
  tableCost n (fun j => compiledCost (BinaryNestedParameterMeasured.environment input x).1.1 (code j))

theorem programs_bound (n : ℕ) (code : Fin n → BinaryExpressionCompiler.Syntax 7)
    (input : Input) (x : SignedWord) (cells frames : ℕ) :
    programs n code input x ≤ 2*listCells (BinaryNestedParameterMeasured.runPrograms n code input x cells frames).1.2 := by
  have h := build_bound n (fun j => BinaryQuadraticSyntaxMeasured.run (BinaryNestedParameterMeasured.environment input x).1.1 (code j))
    (fun j => compiledCost (BinaryNestedParameterMeasured.environment input x).1.1 (code j)) (fun _j => compiled_bound _ _)
  simp only [programs,BinaryNestedParameterMeasured.runPrograms_record,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def parameters (input : Input) : ℕ := programs 9 BinaryNestedParameters.programs input BinaryRationalOpcode.zero

theorem parameters_bound (input : Input) :
    parameters input ≤ 2*listCells (BinaryNestedParameterMeasured.prepare input).1.2 := by
  rw [BinaryNestedParameterMeasured.prepare_record,BinaryNestedParameterMeasured.prepareAt_record]
  exact (
    programs_bound 9 BinaryNestedParameters.programs input BinaryRationalOpcode.zero 128 10
  )

def order (input : Input) : ℕ := BinaryArithmeticEntryWork.comparison input.a input.d+
  BinaryArithmeticEntryWork.raw .minimum input.a input.d+BinaryArithmeticEntryWork.raw .maximum input.a input.d

theorem order_bound (input : Input) : order input ≤ 2*listCells (BinaryNestedOrderMeasured.order input).1.2 := by
  have h0 := comparison_bound input.a input.d
  have h1 := quadratic_bound .minimum input.a input.d
  have h2 := quadratic_bound .maximum input.a input.d
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,order,BinaryNestedOrderMeasured.order_record,BinaryNestedOrderMeasured.collect,
    wrap,combine,listCells_append,listCells_under,listCells]
  omega

def boundary (input : Input) : ℕ :=
  let zero := BinaryQuadraticExpressionMeasured.compare input.q BinaryRationalOpcode.zero
  BinaryArithmeticEntryWork.comparison input.q BinaryRationalOpcode.zero+
    if zero.1.1 then descriptor (BinaryNestedSpecProfile.longInput input) else
      let one := BinaryQuadraticExpressionMeasured.compare BinaryExpressionCompiler.Constant.one.word input.q
      BinaryArithmeticEntryWork.comparison BinaryExpressionCompiler.Constant.one.word input.q+
        if one.1.1 then descriptor (BinaryNestedSpecProfile.shortInput input) else 0

theorem boundary_bound (input : Input) : boundary input ≤ 2*listCells (BinaryNestedBoundaryMeasured.boundary input).1.2 := by
  have hz := comparison_bound input.q BinaryRationalOpcode.zero
  have ho := comparison_bound BinaryExpressionCompiler.Constant.one.word input.q
  have hl := descriptor_bound (BinaryNestedSpecProfile.longInput input)
  have hs := descriptor_bound (BinaryNestedSpecProfile.shortInput input)
  simp only [boundary,BinaryNestedBoundaryMeasured.boundary_record,BinaryNestedBoundaryMeasured.choose]
  split <;> (try split) <;> simp only [BinaryNestedBoundaryMeasured.child_record,BinaryNestedBoundaryMeasured.childFrom,
    wrap,combine,listCells_append,listCells_under,listCells] <;> omega

def classify (input : Input) : ℕ := boundary input+
  match (BinaryNestedBoundaryMeasured.boundary input).1.1 with
  | some _ => 0
  | none => order input

theorem classify_bound (input : Input) : classify input ≤ 2*listCells (BinaryNestedControlMeasured.classify input).1.2 := by
  have hb := boundary_bound input
  have ho := order_bound input
  simp only [classify,BinaryNestedControlMeasured.classify_record]
  cases h : (BinaryNestedBoundaryMeasured.boundary input).1.1 <;>
    simp only [wrap,combine,listCells_append,listCells_under,listCells] <;> omega

def interior (input : Input) : ℕ := classify input+
  match (BinaryNestedControlMeasured.classify input).1.1 with
  | Sum.inl _ => 0
  | Sum.inr ordered => parameters ordered.1

theorem interior_bound (input : Input) : interior input ≤ 2*listCells (BinaryNestedControlMeasured.interior input).1.2 := by
  have hc := classify_bound input
  simp only [interior,BinaryNestedControlMeasured.interior_record]
  cases h : (BinaryNestedControlMeasured.classify input).1.1 with
  | inl table => simp only [wrap,combine,listCells_append,listCells_under,listCells]; omega
  | inr ordered =>
    have hp := parameters_bound ordered.1
    simp only [wrap,combine,listCells_append,listCells_under,listCells]; omega

def regime (input : Input) (params : FixedArrayTable 9 SignedWord) : ℕ :=
  BinaryArithmeticEntryWork.comparison input.t (params.read 2)+
    if (BinaryQuadraticExpressionMeasured.compare input.t (params.read 2)).1.1 then 0
    else BinaryArithmeticEntryWork.comparison (params.read 1) input.t

theorem regime_bound (input : Input) (params : FixedArrayTable 9 SignedWord) :
    regime input params ≤ 2*listCells (BinaryNestedRegimeMeasured.select input params).1.2 := by
  have hf := comparison_bound input.t (params.read 2)
  have hs := comparison_bound (params.read 1) input.t
  simp only [regime,BinaryNestedRegimeMeasured.select]
  split <;> simp only [wrap,combine,listCells_append,listCells_under,listCells] <;> omega

def control (input : Input) : ℕ := interior input+
  match (BinaryNestedControlMeasured.interior input).1.1 with
  | Sum.inl _ => 0
  | Sum.inr prepared => regime prepared.1.1 prepared.2

theorem control_bound (input : Input) : control input ≤ 2*listCells (BinaryNestedControlMeasured.run input).1.2 := by
  have hi := interior_bound input
  simp only [control,BinaryNestedControlMeasured.run_record]
  cases h : (BinaryNestedControlMeasured.interior input).1.1 with
  | inl table => simp only [wrap,combine,listCells_append,listCells_under,listCells]; omega
  | inr prepared =>
    have hr := regime_bound prepared.1.1 prepared.2
    simp only [wrap,combine,listCells_append,listCells_under,listCells]; omega

theorem control_input_bound (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) :
    control input ≤ 2*BinaryNestedControlMeasured.envelope s := by
  have he := control_bound input
  have hu := (BinaryNestedControlMeasured.run_bounds input hC s hs hH).2
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells at hu
  omega

end Blotto.BinaryNestedControlArithmeticEntryWork
