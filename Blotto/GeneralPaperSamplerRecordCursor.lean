import Blotto.GeneralPaperBooleanRecordCursor

/-! Complete retained grouped-sampler field extraction. Concrete tags select
the prepared cache, Boolean cache and actual exponent/address control fields.
The existing measured sampler plan and reserved final record are unchanged. -/
namespace Blotto.GeneralPaperSamplerRecordCursor
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperRetainedScalarValue
open GeneralPaperFieldDirectorySafety GeneralPaperFieldDirectoryPartition
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

inductive Field where | prepared | boolean | controls
def fields : List Field := [.prepared,.boolean,.controls]
def controls (source : GeneralPaperEqualStoredBitSampler.Sampler G l) : List ℕ := [source.exponent,source.address]
def schema (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l) : Field → List ℕ
  | .prepared => (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A source.prepared).sizes
  | .boolean => (GeneralPaperEqualMeasuredRetainedPlan.boolean model S A source.categorical).sizes
  | .controls => (GeneralPaperMeasuredListBlockPlan.run model S A 1 32 (GeneralPaperMeasuredBlockPlan.natural model S) (controls source)).sizes
def child (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l) : Field → ℕ → Directory A
  | .prepared,start => GeneralPaperPreparedRecordCursor.expected model S A source.prepared start
  | .boolean,start => GeneralPaperBooleanRecordCursor.expected model S A source.categorical start
  | .controls,start => GeneralPaperScalarRecordComponents.listExpected model S A start 32 1 ((controls source).map Scalar.natural)
def parser (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l) : GeneralPaperFieldDirectoryParsers.Parser Field A
  | .prepared,regions => GeneralPaperPreparedRecordCursor.run S A source.prepared regions
  | .boolean,regions => GeneralPaperBooleanRecordCursor.run model S A source.categorical regions
  | .controls,regions => GeneralPaperScalarRecordComponents.naturals S A (controls source) regions
def expected (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l) (start : ℕ) : Directory A :=
  GeneralPaperTrailingDirectoryRecord.expected A start 64 (schema model S A source) (child model S A source) fields
def run (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l) (regions : List (Region A)) : GeneralPaperFieldDirectoryParsers.Result A :=
  GeneralPaperTrailingDirectoryRecord.run S A (parser model S A source) fields regions

theorem plan (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l) :
    (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source).sizes = (fields.map (schema model S A source)).flatten ++ [A * 64] := by
  simp only [GeneralPaperEqualMeasuredRetainedPlan.sampler,GeneralPaperMeasuredBlockPlan.sequence_data,
    fields,schema,controls,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,
    GeneralPaperEqualMeasuredLeafPlans.reserve,GeneralPaperMeasuredBlockPlan.references_data,Nat.mul_zero,Nat.zero_add,List.append_assoc]

theorem field_success (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (field : Field) (start : ℕ) (rest : List (Region A)) :
    let regions := (GeneralPaperSequentialLayout.run model S A start (schema model S A source field)).1
    (parser model S A source field (regions ++ rest)).values = some (child model S A source field start) ∧
      (parser model S A source field (regions ++ rest)).remaining = rest ∧
      Safe regions (child model S A source field start) ∧ Covered regions (child model S A source field start) := by
  cases field with
  | prepared => exact GeneralPaperPreparedRecordCursor.success model S A start source.prepared rest
  | boolean => exact GeneralPaperBooleanRecordCursor.success model S A start source.categorical rest
  | controls => exact GeneralPaperScalarRecordComponents.naturals_success model S A start (controls source) rest

theorem success (model : RationalCostModel) (S A start : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l) (rest : List (Region A)) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source)).1
    (run model S A source (regions ++ rest)).values = some (expected model S A source start) ∧
      (run model S A source (regions ++ rest)).remaining = rest ∧
      Safe regions (expected model S A source start) ∧ Covered regions (expected model S A source start) := by
  have hp := fun field start rest => And.intro (field_success model S A source field start rest).1
    (And.intro (field_success model S A source field start rest).2.1 (field_success model S A source field start rest).2.2.1)
  have hc := fun field start => (field_success model S A source field start []).2.2.2
  simpa only [GeneralPaperMeasuredBlockLayout.run,plan,run,expected] using
    GeneralPaperTrailingDirectoryRecord.success model S A (parser model S A source) (schema model S A source)
      (child model S A source) hp hc start 64 fields rest (by decide)

end Blotto.GeneralPaperSamplerRecordCursor
