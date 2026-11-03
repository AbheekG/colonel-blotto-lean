import Blotto.GeneralPaperScalarRecordComponents

/-! Concrete prepared caches compose routes, segments, integer counts,
four natural controls and ONE original-budget scalar. Their existing measured
fields are followed by the reserved 64-word record. Sources are never expanded
by original-budget precision during field extraction. -/
namespace Blotto.GeneralPaperPreparedRecordCursor
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperRetainedScalarValue
open GeneralPaperFieldDirectorySafety GeneralPaperFieldDirectoryPartition
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

inductive Field where | routes | segments | counts | controls | budget
def fields : List Field := [.routes,.segments,.counts,.controls,.budget]
def controls (source : GeneralPaperEqualPreparedCache.Prepared G l) : List ℕ :=
  [source.D,source.rangeBits,source.midpointBits,source.midpointCount]

def schema (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualPreparedCache.Prepared G l) : Field → List ℕ
  | .routes => (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperEqualMeasuredLeafPlans.route model S A) source.routes.table).sizes
  | .segments => (GeneralPaperEqualMeasuredRetainedPlan.segments model S A source.segments).sizes
  | .counts => (GeneralPaperMeasuredArrayBlockPlan.array model S A (GeneralPaperMeasuredBlockPlan.natural model S) source.counts).sizes
  | .controls => (GeneralPaperMeasuredListBlockPlan.run model S A 1 32 (GeneralPaperMeasuredBlockPlan.natural model S) (controls source)).sizes
  | .budget => (GeneralPaperMeasuredBlockPlan.rational model S source.budget).sizes

def child (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualPreparedCache.Prepared G l) : Field → ℕ → Directory A
  | .routes,start => GeneralPaperRouteArrayCursor.expected model S A start source.routes.table
  | .segments,start => GeneralPaperSegmentRecordCursor.expected model S A source.segments start
  | .counts,start => ofArray (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.counts.data.toList.map Scalar.natural))
  | .controls,start => GeneralPaperScalarRecordComponents.listExpected model S A start 32 1 ((controls source).map Scalar.natural)
  | .budget,start => GeneralPaperScalarRecordComponents.leafExpected A start (.rational source.budget)

def parser (S A : ℕ) (source : GeneralPaperEqualPreparedCache.Prepared G l) : GeneralPaperFieldDirectoryParsers.Parser Field A
  | .routes,regions => GeneralPaperRouteArrayCursor.run S A source.routes.table regions
  | .segments,regions => GeneralPaperSegmentRecordCursor.run S A source.segments regions
  | .counts,regions => GeneralPaperFieldDirectoryParsers.natural S A source.counts regions
  | .controls,regions => GeneralPaperScalarRecordComponents.naturals S A (controls source) regions
  | .budget,regions => GeneralPaperScalarRecordComponents.leafRun S A (.rational source.budget) regions

def expected (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualPreparedCache.Prepared G l) (start : ℕ) : Directory A :=
  GeneralPaperTrailingDirectoryRecord.expected A start 64 (schema model S A source) (child model S A source) fields
def run (S A : ℕ) (source : GeneralPaperEqualPreparedCache.Prepared G l) (regions : List (Region A)) : GeneralPaperFieldDirectoryParsers.Result A :=
  GeneralPaperTrailingDirectoryRecord.run S A (parser S A source) fields regions

theorem plan (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualPreparedCache.Prepared G l) :
    (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A source).sizes =
      (fields.map (schema model S A source)).flatten ++ [A * 64] := by
  simp only [GeneralPaperEqualMeasuredRetainedPlan.prepared,GeneralPaperMeasuredBlockPlan.sequence_data,
    fields,schema,controls,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil,
    GeneralPaperEqualMeasuredLeafPlans.reserve,GeneralPaperMeasuredBlockPlan.references_data,Nat.mul_zero,Nat.zero_add,List.append_assoc]

theorem field_success (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualPreparedCache.Prepared G l)
    (field : Field) (start : ℕ) (rest : List (Region A)) :
    let regions := (GeneralPaperSequentialLayout.run model S A start (schema model S A source field)).1
    (parser S A source field (regions ++ rest)).values = some (child model S A source field start) ∧
      (parser S A source field (regions ++ rest)).remaining = rest ∧
      Safe regions (child model S A source field start) ∧ Covered regions (child model S A source field start) := by
  cases field with
  | routes =>
    obtain ⟨hv,hr,hs⟩ := GeneralPaperRouteArrayCursor.success model S A start source.routes.table rest
    exact ⟨hv,hr,hs,GeneralPaperRouteArrayCursor.covered model S A start source.routes.table⟩
  | segments => exact GeneralPaperSegmentRecordCursor.success model S A start source.segments rest
  | counts =>
    obtain ⟨hv,hr,hs⟩ := GeneralPaperFieldDirectoryParsers.natural_success model S A start source.counts rest
    exact ⟨hv,hr,hs,GeneralPaperFieldDirectoryPartition.scalar_natural model S A start source.counts⟩
  | controls => exact GeneralPaperScalarRecordComponents.naturals_success model S A start (controls source) rest
  | budget =>
    simpa only [schema,GeneralPaperMeasuredBlockPlan.rational_data,parser,child,encode] using
      GeneralPaperScalarRecordComponents.leaf_success model S A start (.rational source.budget) rest

theorem success (model : RationalCostModel) (S A start : ℕ) (source : GeneralPaperEqualPreparedCache.Prepared G l) (rest : List (Region A)) :
    let regions := (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A source)).1
    (run S A source (regions ++ rest)).values = some (expected model S A source start) ∧
      (run S A source (regions ++ rest)).remaining = rest ∧
      Safe regions (expected model S A source start) ∧ Covered regions (expected model S A source start) := by
  have hp := fun field start rest => And.intro (field_success model S A source field start rest).1
    (And.intro (field_success model S A source field start rest).2.1 (field_success model S A source field start rest).2.2.1)
  have hc := fun field start => (field_success model S A source field start []).2.2.2
  simpa only [GeneralPaperMeasuredBlockLayout.run,plan,run,expected] using
    GeneralPaperTrailingDirectoryRecord.success model S A (parser S A source) (schema model S A source)
      (child model S A source) hp hc start 64 fields rest (by decide)

end Blotto.GeneralPaperPreparedRecordCursor
