import Blotto.GeneralPaperNestedArrayFieldCursor

/-! Concrete endpoint-matrix field extraction fixes every child parser to
the checked rational-array parser. Existing measured nested-array regions
supply outer/row headers and scalar cells in order, without remeasurement or
an externally supplied field directory. The following stream is untouched. -/
namespace Blotto.GeneralPaperMatrixFieldCursor
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperFieldDirectorySafety
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def rowSchema {m : ℕ} (model : RationalCostModel) (S A : ℕ) (row : FixedArrayTable m ℚ) : List ℕ :=
  (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.rational model S) row).sizes

def rowExpected {m : ℕ} (model : RationalCostModel) (S A : ℕ) (row : FixedArrayTable m ℚ) (start : ℕ) : Directory A :=
  ofArray (GeneralPaperMappedScalarArrayCursor.expected model S A start
    (row.data.toList.map GeneralPaperRetainedScalarValue.Scalar.rational))

def expected {m r : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable r (FixedArrayTable m ℚ)) : Directory A :=
  GeneralPaperNestedArrayFieldCursor.compose (GeneralPaperScalarArrayFieldCursor.layoutHeader A start source.data.toList.length)
    (GeneralPaperChildDirectorySpecification.collect
      (GeneralPaperChildDirectorySpecification.directories (rowSchema model S A) (rowExpected model S A)
        (start + A * (64 + source.data.toList.length)) source.data.toList))

def run {m r : ℕ} (S A : ℕ) (source : FixedArrayTable r (FixedArrayTable m ℚ)) (regions : List (Region A)) :
    GeneralPaperFieldDirectoryParsers.Result A :=
  GeneralPaperNestedArrayFieldCursor.runList S A (GeneralPaperFieldDirectoryParsers.rational S A) source.data.toList regions

theorem plan {m r : ℕ} (model : RationalCostModel) (S A : ℕ) (source : FixedArrayTable r (FixedArrayTable m ℚ)) :
    (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source).sizes =
      A * (64 + source.data.toList.length) :: (source.data.toList.map (rowSchema model S A)).flatten := by
  have hMap := congrArg (List.map (rowSchema model S A)) (GeneralPaperRowPrefix.list_ofFn source)
  simp only [List.map_ofFn,Function.comp_def] at hMap
  unfold GeneralPaperEqualMeasuredRetainedPlan.matrix
  rw [GeneralPaperMeasuredArrayBlockPlan.array_data]
  change A * (r + 64) :: (List.ofFn (fun i : Fin r => rowSchema model S A (source.read i))).flatten = _
  rw [hMap,Array.length_toList,source.size]
  congr 1
  ring

theorem success {m r : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable r (FixedArrayTable m ℚ))
    (rest : List (Region A)) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source)).1
    (run S A source (regions ++ rest)).values = some (expected model S A start source) ∧
      (run S A source (regions ++ rest)).remaining = rest ∧ Safe regions (expected model S A start source) := by
  have hParser : ∀ row : FixedArrayTable m ℚ,∀ start rest,
      (GeneralPaperFieldDirectoryParsers.rational S A row
        ((GeneralPaperSequentialLayout.run model S A start (rowSchema model S A row)).1 ++ rest)).values =
          some (rowExpected model S A row start) ∧
      (GeneralPaperFieldDirectoryParsers.rational S A row
        ((GeneralPaperSequentialLayout.run model S A start (rowSchema model S A row)).1 ++ rest)).remaining = rest ∧
      Safe (GeneralPaperSequentialLayout.run model S A start (rowSchema model S A row)).1 (rowExpected model S A row start) := by
    intro row start rest
    exact GeneralPaperFieldDirectoryParsers.rational_success model S A start row rest
  simpa only [GeneralPaperMeasuredBlockLayout.run,plan,expected,run] using
    GeneralPaperNestedArrayFieldCursor.success model S A (GeneralPaperFieldDirectoryParsers.rational S A)
      (rowSchema model S A) (rowExpected model S A) hParser start source.data.toList rest

theorem root {m r : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable r (FixedArrayTable m ℚ)) :
    (expected model S A start source).root = GeneralPaperScalarArrayFieldCursor.layoutHeader A start r := by
  change GeneralPaperScalarArrayFieldCursor.layoutHeader A start source.data.toList.length = _
  rw [Array.length_toList,source.size]

theorem outer_target_count {m r : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedArrayTable r (FixedArrayTable m ℚ)) :
    ((expected model S A start source).headers.head?).map (fun header => header.targets.length) = some r := by
  simp only [expected,GeneralPaperNestedArrayFieldCursor.compose,GeneralPaperChildDirectorySpecification.collect,
    List.head?_cons,Option.map_some,List.length_map,GeneralPaperChildDirectorySpecification.directory_count,Array.length_toList,source.size]

end Blotto.GeneralPaperMatrixFieldCursor
