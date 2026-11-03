import Blotto.GeneralPaperStoredGroupedOuterContract

/-! Complete dominant-branch directory: the retained rational row, chosen
natural label and existing trailing 32-word record use the unchanged plan.
One forward parser consumes these actual regions with a complete owner partition. -/
namespace Blotto.GeneralPaperStoredDominantCursor
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperRetainedScalarValue
open GeneralPaperFieldDirectorySafety GeneralPaperFieldDirectoryPartition
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 8192

inductive Field where | row | chosen

def fields : List Field := [.row,.chosen]
def rowTable {n : ℕ} (source : RationalResourceArray n) : FixedArrayTable n ℚ := ⟨source.data,source.size⟩
def schema {n : ℕ} (model : RationalCostModel) (S A chosen : ℕ) (source : RationalResourceArray n) : Field → List ℕ
  | .row => (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.rational model S) (rowTable source)).sizes
  | .chosen => (GeneralPaperMeasuredBlockPlan.natural model S chosen).sizes

def child {n : ℕ} (model : RationalCostModel) (S A chosen : ℕ) (source : RationalResourceArray n) : Field → ℕ → Directory A
  | .row,start => ofArray (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.rational))
  | .chosen,start => GeneralPaperScalarRecordComponents.leafExpected A start (.natural chosen)

def parser {n : ℕ} (S A chosen : ℕ) (source : RationalResourceArray n) : GeneralPaperFieldDirectoryParsers.Parser Field A
  | .row,regions => GeneralPaperFieldDirectoryParsers.rational S A (rowTable source) regions
  | .chosen,regions => GeneralPaperScalarRecordComponents.leafRun S A (.natural chosen) regions

def plan {n : ℕ} (model : RationalCostModel) (S A chosen : ℕ) (source : RationalResourceArray n) :=
  GeneralPaperMeasuredBlockPlan.sequence S
    [GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.rational model S) (rowTable source),
      GeneralPaperMeasuredBlockPlan.natural model S chosen,GeneralPaperEqualMeasuredLeafPlans.reserve model S A 32]

def expected {n : ℕ} (model : RationalCostModel) (S A chosen : ℕ) (source : RationalResourceArray n) (start : ℕ) : Directory A :=
  GeneralPaperTrailingDirectoryRecord.expected A start 32 (schema model S A chosen source) (child model S A chosen source) fields

def run {n : ℕ} (S A chosen : ℕ) (source : RationalResourceArray n) (regions : List (Region A)) : GeneralPaperFieldDirectoryParsers.Result A :=
  GeneralPaperTrailingDirectoryRecord.run S A (parser S A chosen source) fields regions

theorem plan_data {n : ℕ} (model : RationalCostModel) (S A chosen : ℕ) (source : RationalResourceArray n) :
    (plan model S A chosen source).sizes = (fields.map (schema model S A chosen source)).flatten ++ [A * 32] := by
  simp only [plan,GeneralPaperMeasuredBlockPlan.sequence_data,fields,schema,List.map_cons,List.map_nil,
    List.flatten_cons,List.flatten_nil,List.append_nil,GeneralPaperEqualMeasuredLeafPlans.reserve,
    GeneralPaperMeasuredBlockPlan.references_data,Nat.mul_zero,Nat.zero_add,List.append_assoc]

theorem field_success {n : ℕ} (model : RationalCostModel) (S A chosen : ℕ) (source : RationalResourceArray n)
    (field : Field) (start : ℕ) (rest : List (Region A)) :
    let regions := (GeneralPaperSequentialLayout.run model S A start (schema model S A chosen source field)).1
    (parser S A chosen source field (regions ++ rest)).values = some (child model S A chosen source field start) ∧
      (parser S A chosen source field (regions ++ rest)).remaining = rest ∧
      Safe regions (child model S A chosen source field start) ∧ Covered regions (child model S A chosen source field start) := by
  cases field with
  | row =>
    obtain ⟨hv,hr,hs⟩ := GeneralPaperFieldDirectoryParsers.rational_success model S A start (rowTable source) rest
    exact ⟨hv,hr,hs,GeneralPaperFieldDirectoryPartition.scalar_rational model S A start (rowTable source)⟩
  | chosen =>
    simpa only [schema,GeneralPaperMeasuredBlockPlan.natural_data,encode,parser,child] using
      GeneralPaperScalarRecordComponents.leaf_success model S A start (.natural chosen) rest

theorem success {n : ℕ} (model : RationalCostModel) (S A start chosen : ℕ) (source : RationalResourceArray n) (rest : List (Region A)) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start (plan model S A chosen source)).1
    (run S A chosen source (regions ++ rest)).values = some (expected model S A chosen source start) ∧
      (run S A chosen source (regions ++ rest)).remaining = rest ∧
      Safe regions (expected model S A chosen source start) ∧ Covered regions (expected model S A chosen source start) := by
  have hp := fun field start rest => And.intro (field_success model S A chosen source field start rest).1
    (And.intro (field_success model S A chosen source field start rest).2.1 (field_success model S A chosen source field start rest).2.2.1)
  have hc := fun field start => (field_success model S A chosen source field start []).2.2.2
  simpa only [GeneralPaperMeasuredBlockLayout.run,plan_data,run,expected] using
    GeneralPaperTrailingDirectoryRecord.success model S A (parser S A chosen source) (schema model S A chosen source)
      (child model S A chosen source) hp hc start 32 fields rest (by decide)

theorem positive {n : ℕ} (model : RationalCostModel) (S A chosen : ℕ) (source : RationalResourceArray n) (hA : 0 < A) :
    GeneralPaperMeasuredPlanPositive.Positive (plan model S A chosen source) := by
  apply GeneralPaperMeasuredPlanPositive.sequence
  intro p hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact GeneralPaperMeasuredPlanPositive.array model S A _ (rowTable source) hA
      (fun j => GeneralPaperMeasuredPlanPositive.rational model S _)
  · exact GeneralPaperMeasuredPlanPositive.natural model S chosen
  · exact GeneralPaperMeasuredPlanPositive.references model S A 0 0 32 hA (by decide)

end Blotto.GeneralPaperStoredDominantCursor
