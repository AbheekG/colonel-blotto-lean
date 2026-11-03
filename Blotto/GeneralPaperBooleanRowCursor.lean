import Blotto.GeneralPaperBooleanWordCursor

/-! Labelled Boolean rows retain their actual natural label and stored word,
then use the existing 16-word record. The concrete row-list cursor fixes that
parser and preserves the old 32-prefix/two-word-per-row measured plan. -/
namespace Blotto.GeneralPaperBooleanRowCursor
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperRetainedScalarValue
open GeneralPaperFieldDirectorySafety GeneralPaperFieldDirectoryPartition
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

inductive Field where | label | word
def fields : List Field := [.label,.word]
def schema {r w : ℕ} (model : RationalCostModel) (S A : ℕ) (source : Fin r × FixedBinaryWord w) : Field → List ℕ
  | .label => (GeneralPaperMeasuredBlockPlan.natural model S source.1.val).sizes
  | .word => (GeneralPaperEqualMeasuredLeafPlans.word model S A source.2).sizes
def child {r w : ℕ} (model : RationalCostModel) (S A : ℕ) (source : Fin r × FixedBinaryWord w) : Field → ℕ → Directory A
  | .label,start => GeneralPaperScalarRecordComponents.leafExpected A start (.natural source.1.val)
  | .word,start => GeneralPaperBooleanWordCursor.expected model S A source.2 start
def parser {r w : ℕ} (S A : ℕ) (source : Fin r × FixedBinaryWord w) : GeneralPaperFieldDirectoryParsers.Parser Field A
  | .label,regions => GeneralPaperScalarRecordComponents.leafRun S A (.natural source.1.val) regions
  | .word,regions => GeneralPaperBooleanWordCursor.run S A source.2 regions
def expected {r w : ℕ} (model : RationalCostModel) (S A : ℕ) (source : Fin r × FixedBinaryWord w) (start : ℕ) : Directory A :=
  GeneralPaperTrailingDirectoryRecord.expected A start 16 (schema model S A source) (child model S A source) fields
def run {r w : ℕ} (S A : ℕ) (source : Fin r × FixedBinaryWord w) (regions : List (Region A)) : GeneralPaperFieldDirectoryParsers.Result A :=
  GeneralPaperTrailingDirectoryRecord.run S A (parser S A source) fields regions

theorem plan {r w : ℕ} (model : RationalCostModel) (S A : ℕ) (source : Fin r × FixedBinaryWord w) :
    (GeneralPaperEqualMeasuredLeafPlans.row model S A source).sizes = (fields.map (schema model S A source)).flatten ++ [A * 16] := by
  simp only [GeneralPaperEqualMeasuredLeafPlans.row,GeneralPaperMeasuredBlockPlan.sequence_data,
    fields,schema,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,
    GeneralPaperEqualMeasuredLeafPlans.reserve,GeneralPaperMeasuredBlockPlan.references_data,Nat.mul_zero,Nat.zero_add,List.append_assoc]

theorem field_success {r w : ℕ} (model : RationalCostModel) (S A : ℕ) (source : Fin r × FixedBinaryWord w)
    (field : Field) (start : ℕ) (rest : List (Region A)) :
    let regions := (GeneralPaperSequentialLayout.run model S A start (schema model S A source field)).1
    (parser S A source field (regions ++ rest)).values = some (child model S A source field start) ∧
      (parser S A source field (regions ++ rest)).remaining = rest ∧
      Safe regions (child model S A source field start) ∧ Covered regions (child model S A source field start) := by
  cases field with
  | label =>
    simpa only [schema,GeneralPaperMeasuredBlockPlan.natural_data,parser,child,encode] using
      GeneralPaperScalarRecordComponents.leaf_success model S A start (.natural source.1.val) rest
  | word => exact GeneralPaperBooleanWordCursor.success model S A start source.2 rest

theorem success {r w : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : Fin r × FixedBinaryWord w) (rest : List (Region A)) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredLeafPlans.row model S A source)).1
    (run S A source (regions ++ rest)).values = some (expected model S A source start) ∧
      (run S A source (regions ++ rest)).remaining = rest ∧
      Safe regions (expected model S A source start) ∧ Covered regions (expected model S A source start) := by
  have hp := fun field start rest => And.intro (field_success model S A source field start rest).1
    (And.intro (field_success model S A source field start rest).2.1 (field_success model S A source field start rest).2.2.1)
  have hc := fun field start => (field_success model S A source field start []).2.2.2
  simpa only [GeneralPaperMeasuredBlockLayout.run,plan,run,expected] using
    GeneralPaperTrailingDirectoryRecord.success model S A (parser S A source) (schema model S A source)
      (child model S A source) hp hc start 16 fields rest (by decide)

def rowsExpected {r w : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : List (Fin r × FixedBinaryWord w)) : Directory A :=
  GeneralPaperFrontDirectoryList.expected A start (fun row => (GeneralPaperEqualMeasuredLeafPlans.row model S A row).sizes)
    (expected model S A) source
def rowsRun {r w : ℕ} (S A : ℕ) (source : List (Fin r × FixedBinaryWord w)) (regions : List (Region A)) : GeneralPaperFieldDirectoryParsers.Result A :=
  GeneralPaperFrontDirectoryList.run S A (run S A) source regions

theorem rows_success {r w : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : List (Fin r × FixedBinaryWord w)) (rest : List (Region A)) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start
      (GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (GeneralPaperEqualMeasuredLeafPlans.row model S A) source)).1
    (rowsRun S A source (regions ++ rest)).values = some (rowsExpected model S A start source) ∧
      (rowsRun S A source (regions ++ rest)).remaining = rest ∧
      Safe regions (rowsExpected model S A start source) ∧ Covered regions (rowsExpected model S A start source) := by
  have hp := fun (row : Fin r × FixedBinaryWord w) start rest => And.intro (success model S A start row rest).1
    (And.intro (success model S A start row rest).2.1 (success model S A start row rest).2.2.1)
  have hc := fun (row : Fin r × FixedBinaryWord w) start => (success model S A start row []).2.2.2
  simpa only [GeneralPaperMeasuredBlockLayout.run,GeneralPaperMeasuredListBlockPlan.data,List.singleton_append,rowsRun,rowsExpected] using
    GeneralPaperFrontDirectoryList.success model S A (run S A)
      (fun row => (GeneralPaperEqualMeasuredLeafPlans.row model S A row).sizes) (expected model S A) hp hc start source rest

end Blotto.GeneralPaperBooleanRowCursor
