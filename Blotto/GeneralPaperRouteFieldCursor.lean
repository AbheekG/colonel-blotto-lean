import Blotto.GeneralPaperTrailingScalarRecord

/-! Concrete retained routes use their existing measured layout: a presence
bit, optional natural group label, rational coefficient, then 16 root words.
Both route cases are extracted without remeasurement or a supplied schema. -/
namespace Blotto.GeneralPaperRouteFieldCursor
open GeneralPaperSequentialLayout GeneralPaperFieldDirectory GeneralPaperRetainedScalarValue
open GeneralPaperFieldDirectorySafety GeneralPaperFieldDirectoryPartition
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

def values {m : ℕ} (source : GroupRoute m) : List Scalar :=
  match source.1 with
  | none => [.bit false,.rational source.2]
  | some group => [.bit true,.natural group.val,.rational source.2]

def copy {m : ℕ} (S A : ℕ) (source : GroupRoute m) : List Scalar × ℕ :=
  let actual := values source
  (actual,(actual.map encode).sum + 192 * (S + A + 1))

def run {m : ℕ} (S A : ℕ) (source : GroupRoute m) (regions : List (Region A)) : GeneralPaperFieldDirectoryParsers.Result A :=
  let copied := copy S A source
  let parsed := GeneralPaperTrailingScalarRecord.run S A copied.1 regions
  ⟨parsed.values,parsed.remaining,copied.2 + parsed.work + 64 * (S + A + 1)⟩

def expected {m : ℕ} (model : RationalCostModel) (S A : ℕ) (source : GroupRoute m) (start : ℕ) : Directory A :=
  GeneralPaperTrailingScalarRecord.expected model S A start 16 (values source)

theorem plan {m : ℕ} (model : RationalCostModel) (S A : ℕ) (source : GroupRoute m) :
    (GeneralPaperEqualMeasuredLeafPlans.route model S A source).sizes = (values source).map encode ++ [A * 16] := by
  rcases source with ⟨label,coefficient⟩
  cases label <;>
    simp only [GeneralPaperEqualMeasuredLeafPlans.route,GeneralPaperMeasuredBlockPlan.sequence_data,
      GeneralPaperEqualMeasuredLeafPlans.tag,GeneralPaperEqualMeasuredLeafPlans.empty,
      GeneralPaperMeasuredBlockPlan.natural_data,GeneralPaperMeasuredBlockPlan.rational_data,
      GeneralPaperEqualMeasuredLeafPlans.reserve,GeneralPaperMeasuredBlockPlan.references_data,
      List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.nil_append,List.cons_append,List.append_nil,
      values,encode,Nat.mul_zero,Nat.zero_add,Nat.mul_comm]

theorem value_count {m : ℕ} (source : GroupRoute m) : (values source).length ≤ 16 := by
  rcases source with ⟨label,coefficient⟩
  cases label <;> simp only [values,List.length_cons,List.length_nil] <;> omega

theorem success {m : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : GroupRoute m) (rest : List (Region A)) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredLeafPlans.route model S A source)).1
    (run S A source (regions ++ rest)).values = some (expected model S A source start) ∧
      (run S A source (regions ++ rest)).remaining = rest ∧ Safe regions (expected model S A source start) ∧
      Covered regions (expected model S A source start) := by
  simpa only [GeneralPaperMeasuredBlockLayout.run,plan,run,copy,expected] using
    GeneralPaperTrailingScalarRecord.success model S A start 16 (values source) rest (value_count source)

theorem root {m : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : GroupRoute m) :
    (expected model S A source start).root = GeneralPaperTrailingScalarRecord.header A
      (start + ((values source).map encode).sum) 16 := rfl

theorem work {m : ℕ} (S A : ℕ) (source : GroupRoute m) (regions : List (Region A)) :
    (run S A source regions).work = (GeneralPaperTrailingScalarRecord.run S A (values source) regions).work +
      ((values source).map encode).sum + 256 * (S + A + 1) := by
  dsimp only [run,copy]
  ring

end Blotto.GeneralPaperRouteFieldCursor
