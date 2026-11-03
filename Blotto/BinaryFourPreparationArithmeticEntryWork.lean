import Blotto.BinaryGroupArithmeticEntryWork
import Blotto.BinaryFourOrderMeasured
import Blotto.BinaryFourGuardMeasured
import Blotto.BinaryFourParametersMeasured

/-! Entry accounting follows actual sorting permutations, the reached four-word
branch guard and the shared eight-word parameter table. Returned arithmetic
words and compiled programs, rather than logical substitutes, feed later costs. -/
namespace Blotto.BinaryFourPreparationArithmeticEntryWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryExpressionArithmeticEntryWork (tableCost build_bound quadratic_bound comparison_bound)
open BinaryThreeFactoryArithmeticEntryWork (compiledCost compiled_bound)
set_option autoImplicit false
set_option maxHeartbeats 5000000

def compare (length : Fin 3 → SignedWord) (i j : Fin 3) : ℕ :=
  BinaryArithmeticEntryWork.comparison (length i) (length j)

theorem compare_bound (length : Fin 3 → SignedWord) (i j : Fin 3) :
    compare length i j ≤ 2*listCells (BinaryFourOrderMeasured.compare length i j).1.2 := by
  have h := comparison_bound (length i) (length j)
  simp only [compare,BinaryFourOrderMeasured.compare,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def sort (length : Fin 3 → SignedWord) : ℕ :=
  let first := BinaryFourOrderMeasured.compare length 0 1
  let middle := fun j => length (first.1.1 j)
  let second := BinaryFourOrderMeasured.compare middle 1 2
  let last := fun j => middle (second.1.1 j)
  compare length 0 1+compare middle 1 2+compare last 0 1

theorem sort_bound (length : Fin 3 → SignedWord) :
    sort length ≤ 2*listCells (BinaryFourOrderMeasured.sort length).1.2 := by
  let first := BinaryFourOrderMeasured.compare length 0 1
  let middle := fun j => length (first.1.1 j)
  let second := BinaryFourOrderMeasured.compare middle 1 2
  let last := fun j => middle (second.1.1 j)
  have hf := compare_bound length 0 1
  have hs := compare_bound middle 1 2
  have ht := compare_bound last 0 1
  dsimp only [last,second,middle,first] at hs ht
  simp only [sort,BinaryFourOrderMeasured.sort,wrap,combine,listCells_append,listCells_under,listCells]
  omega

theorem ordered_bound (input : BinaryFourSpecSampler.Input) :
    sort input.length.read ≤ 2*listCells (BinaryFourOrderMeasured.ordered input).1.2 := by
  have h := sort_bound input.length.read
  simp only [BinaryFourOrderMeasured.ordered,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def guard (input : BinaryFourParameters.Input) : ℕ :=
  let complement := BinaryQuadraticMeasured.apply .sub BinaryExpressionCompiler.Constant.one.word input.p
  let threshold := BinaryQuadraticMeasured.apply .mul complement.1.1 input.ell
  BinaryArithmeticEntryWork.raw .sub BinaryExpressionCompiler.Constant.one.word input.p+
    BinaryArithmeticEntryWork.raw .mul complement.1.1 input.ell+
    BinaryArithmeticEntryWork.comparison threshold.1.1 input.w

theorem guard_bound (input : BinaryFourParameters.Input) :
    guard input ≤ 2*listCells (BinaryFourGuardMeasured.guard input).1.2 := by
  have hc := quadratic_bound .sub BinaryExpressionCompiler.Constant.one.word input.p
  have ht := quadratic_bound .mul (BinaryQuadraticMeasured.apply .sub BinaryExpressionCompiler.Constant.one.word input.p).1.1 input.ell
  have hg := comparison_bound
    (BinaryQuadraticMeasured.apply .mul (BinaryQuadraticMeasured.apply .sub BinaryExpressionCompiler.Constant.one.word input.p).1.1 input.ell).1.1 input.w
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,guard,BinaryFourGuardMeasured.guard_record,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def parameters (input : BinaryFourParameters.Input) : ℕ :=
  let env := BinaryFourParametersMeasured.environment input
  tableCost 8 (fun j => compiledCost env.1.1 (BinaryFourParameters.programs j))

theorem parameters_bound (input : BinaryFourParameters.Input) :
    parameters input ≤ 2*listCells (BinaryFourParametersMeasured.prepare input).1.2 := by
  have h := build_bound 8
    (fun j => BinaryQuadraticSyntaxMeasured.run (BinaryFourParametersMeasured.environment input).1.1 (BinaryFourParameters.programs j))
    (fun j => compiledCost (BinaryFourParametersMeasured.environment input).1.1 (BinaryFourParameters.programs j))
    (fun j => compiled_bound _ _)
  simp only [parameters,BinaryFourParametersMeasured.prepare_record,wrap,combine,listCells_append,listCells_under,listCells]
  omega

end Blotto.BinaryFourPreparationArithmeticEntryWork
