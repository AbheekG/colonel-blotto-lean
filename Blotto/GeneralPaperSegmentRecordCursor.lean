import Blotto.GeneralPaperTrailingDirectoryRecord

/-! Concrete segment records compose the existing weight array and two
endpoint matrices, followed by their existing 32-word reserved record.
The field tag fixes each checked parser; no schema is an execution input. -/
namespace Blotto.GeneralPaperSegmentRecordCursor
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperRetainedScalarValue
open GeneralPaperFieldDirectorySafety GeneralPaperFieldDirectoryPartition
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

inductive Field where | weights | left | right
def fields : List Field := [.weights,.left,.right]

def schema {m r : ℕ} {l : RationalSegmentLottery m r} (model : RationalCostModel) (S A : ℕ)
    (source : PreparedSegmentDescriptor l) : Field → List ℕ
  | .weights => (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.rational model S) source.weights).sizes
  | .left => (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source.left).sizes
  | .right => (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source.right).sizes

def child {m r : ℕ} {l : RationalSegmentLottery m r} (model : RationalCostModel) (S A : ℕ)
    (source : PreparedSegmentDescriptor l) : Field → ℕ → Directory A
  | .weights,start => ofArray (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.weights.data.toList.map Scalar.rational))
  | .left,start => GeneralPaperMatrixFieldCursor.expected model S A start source.left
  | .right,start => GeneralPaperMatrixFieldCursor.expected model S A start source.right

def parser {m r : ℕ} {l : RationalSegmentLottery m r} (S A : ℕ) (source : PreparedSegmentDescriptor l) :
    GeneralPaperFieldDirectoryParsers.Parser Field A
  | .weights,regions => GeneralPaperFieldDirectoryParsers.rational S A source.weights regions
  | .left,regions => GeneralPaperMatrixFieldCursor.run S A source.left regions
  | .right,regions => GeneralPaperMatrixFieldCursor.run S A source.right regions

def expected {m r : ℕ} {l : RationalSegmentLottery m r} (model : RationalCostModel) (S A : ℕ)
    (source : PreparedSegmentDescriptor l) (start : ℕ) : Directory A :=
  GeneralPaperTrailingDirectoryRecord.expected A start 32 (schema model S A source) (child model S A source) fields

def run {m r : ℕ} {l : RationalSegmentLottery m r} (S A : ℕ) (source : PreparedSegmentDescriptor l) (regions : List (Region A)) :
    GeneralPaperFieldDirectoryParsers.Result A := GeneralPaperTrailingDirectoryRecord.run S A (parser S A source) fields regions

theorem plan {m r : ℕ} {l : RationalSegmentLottery m r} (model : RationalCostModel) (S A : ℕ) (source : PreparedSegmentDescriptor l) :
    (GeneralPaperEqualMeasuredRetainedPlan.segments model S A source).sizes = (fields.map (schema model S A source)).flatten ++ [A * 32] := by
  simp only [GeneralPaperEqualMeasuredRetainedPlan.segments,GeneralPaperMeasuredBlockPlan.sequence_data,
    fields,schema,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,
    GeneralPaperEqualMeasuredLeafPlans.reserve,GeneralPaperMeasuredBlockPlan.references_data,Nat.mul_zero,Nat.zero_add,List.append_assoc]

theorem field_success {m r : ℕ} {l : RationalSegmentLottery m r} (model : RationalCostModel) (S A : ℕ)
    (source : PreparedSegmentDescriptor l) (field : Field) (start : ℕ) (rest : List (Region A)) :
    let regions := (GeneralPaperSequentialLayout.run model S A start (schema model S A source field)).1
    (parser S A source field (regions ++ rest)).values = some (child model S A source field start) ∧
      (parser S A source field (regions ++ rest)).remaining = rest ∧
      Safe regions (child model S A source field start) ∧ Covered regions (child model S A source field start) := by
  cases field with
  | weights =>
    obtain ⟨hv,hr,hs⟩ := GeneralPaperFieldDirectoryParsers.rational_success model S A start source.weights rest
    exact ⟨hv,hr,hs,GeneralPaperFieldDirectoryPartition.scalar_rational model S A start source.weights⟩
  | left =>
    obtain ⟨hv,hr,hs⟩ := GeneralPaperMatrixFieldCursor.success model S A start source.left rest
    exact ⟨hv,hr,hs,GeneralPaperFieldDirectoryPartition.matrix model S A start source.left⟩
  | right =>
    obtain ⟨hv,hr,hs⟩ := GeneralPaperMatrixFieldCursor.success model S A start source.right rest
    exact ⟨hv,hr,hs,GeneralPaperFieldDirectoryPartition.matrix model S A start source.right⟩

theorem success {m r : ℕ} {l : RationalSegmentLottery m r} (model : RationalCostModel) (S A start : ℕ)
    (source : PreparedSegmentDescriptor l) (rest : List (Region A)) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.segments model S A source)).1
    (run S A source (regions ++ rest)).values = some (expected model S A source start) ∧
      (run S A source (regions ++ rest)).remaining = rest ∧
      Safe regions (expected model S A source start) ∧ Covered regions (expected model S A source start) := by
  have hp : ∀ field start rest,
      (parser S A source field ((GeneralPaperSequentialLayout.run model S A start (schema model S A source field)).1 ++ rest)).values =
        some (child model S A source field start) ∧
      (parser S A source field ((GeneralPaperSequentialLayout.run model S A start (schema model S A source field)).1 ++ rest)).remaining = rest ∧
      Safe (GeneralPaperSequentialLayout.run model S A start (schema model S A source field)).1 (child model S A source field start) := by
    intro field start rest
    obtain ⟨hv,hr,hs,_⟩ := field_success model S A source field start rest
    exact ⟨hv,hr,hs⟩
  have hc := fun field start => (field_success model S A source field start []).2.2.2
  simpa only [GeneralPaperMeasuredBlockLayout.run,plan,run,expected] using
    GeneralPaperTrailingDirectoryRecord.success model S A (parser S A source) (schema model S A source)
      (child model S A source) hp hc start 32 fields rest (by decide)

end Blotto.GeneralPaperSegmentRecordCursor
