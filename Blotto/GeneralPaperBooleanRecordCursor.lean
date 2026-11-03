import Blotto.GeneralPaperRulerFieldCursor

/-! Concrete Boolean caches fix the denominator-word, labelled-row-list and
unit-ruler parsers. The complete existing measured field order and reserved
64-word record are retained, with checked owner partition and continuation. -/
namespace Blotto.GeneralPaperBooleanRecordCursor
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperFieldDirectorySafety GeneralPaperFieldDirectoryPartition
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
variable {prepared : GeneralPaperEqualPreparedCache.Prepared G l}

inductive Field where | denominator | rows | ruler
def fields : List Field := [.denominator,.rows,.ruler]
def schema (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualBooleanCache.Cache prepared) : Field → List ℕ
  | .denominator => (GeneralPaperEqualMeasuredLeafPlans.word model S A source.denominator).sizes
  | .rows => (GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (GeneralPaperEqualMeasuredLeafPlans.row model S A) source.rows).sizes
  | .ruler => (GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (GeneralPaperEqualMeasuredLeafPlans.unit S) source.ruler).sizes
def child (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualBooleanCache.Cache prepared) : Field → ℕ → Directory A
  | .denominator,start => GeneralPaperBooleanWordCursor.expected model S A source.denominator start
  | .rows,start => GeneralPaperBooleanRowCursor.rowsExpected model S A start source.rows
  | .ruler,start => GeneralPaperRulerFieldCursor.expected A start source.ruler
def parser (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualBooleanCache.Cache prepared) : GeneralPaperFieldDirectoryParsers.Parser Field A
  | .denominator,regions => GeneralPaperBooleanWordCursor.run S A source.denominator regions
  | .rows,regions => GeneralPaperBooleanRowCursor.rowsRun S A source.rows regions
  | .ruler,regions => GeneralPaperRulerFieldCursor.run model S A source.ruler regions
def expected (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualBooleanCache.Cache prepared) (start : ℕ) : Directory A :=
  GeneralPaperTrailingDirectoryRecord.expected A start 64 (schema model S A source) (child model S A source) fields
def run (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualBooleanCache.Cache prepared) (regions : List (Region A)) : GeneralPaperFieldDirectoryParsers.Result A :=
  GeneralPaperTrailingDirectoryRecord.run S A (parser model S A source) fields regions

theorem plan (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualBooleanCache.Cache prepared) :
    (GeneralPaperEqualMeasuredRetainedPlan.boolean model S A source).sizes = (fields.map (schema model S A source)).flatten ++ [A * 64] := by
  simp only [GeneralPaperEqualMeasuredRetainedPlan.boolean,GeneralPaperMeasuredBlockPlan.sequence_data,
    fields,schema,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,
    GeneralPaperEqualMeasuredLeafPlans.reserve,GeneralPaperMeasuredBlockPlan.references_data,Nat.mul_zero,Nat.zero_add,List.append_assoc]

theorem field_success (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualBooleanCache.Cache prepared)
    (field : Field) (start : ℕ) (rest : List (Region A)) :
    let regions := (GeneralPaperSequentialLayout.run model S A start (schema model S A source field)).1
    (parser model S A source field (regions ++ rest)).values = some (child model S A source field start) ∧
      (parser model S A source field (regions ++ rest)).remaining = rest ∧
      Safe regions (child model S A source field start) ∧ Covered regions (child model S A source field start) := by
  cases field with
  | denominator => exact GeneralPaperBooleanWordCursor.success model S A start source.denominator rest
  | rows => exact GeneralPaperBooleanRowCursor.rows_success model S A start source.rows rest
  | ruler => exact GeneralPaperRulerFieldCursor.success model S A start source.ruler rest

theorem success (model : RationalCostModel) (S A start : ℕ) (source : GeneralPaperEqualBooleanCache.Cache prepared) (rest : List (Region A)) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.boolean model S A source)).1
    (run model S A source (regions ++ rest)).values = some (expected model S A source start) ∧
      (run model S A source (regions ++ rest)).remaining = rest ∧
      Safe regions (expected model S A source start) ∧ Covered regions (expected model S A source start) := by
  have hp := fun field start rest => And.intro (field_success model S A source field start rest).1
    (And.intro (field_success model S A source field start rest).2.1 (field_success model S A source field start rest).2.2.1)
  have hc := fun field start => (field_success model S A source field start []).2.2.2
  simpa only [GeneralPaperMeasuredBlockLayout.run,plan,run,expected] using
    GeneralPaperTrailingDirectoryRecord.success model S A (parser model S A source) (schema model S A source)
      (child model S A source) hp hc start 64 fields rest (by decide)

end Blotto.GeneralPaperBooleanRecordCursor
