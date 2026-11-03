import Blotto.GeneralPaperEqualDrawDescription

/-! The real-model returned record has no categorical integer denominator,
count array, rejection width or Boolean cache. The full-cache view below is
noncomputable analysis and is never called by preparation or the real draw. -/
namespace Blotto.GeneralPaperEqualRealCache
open GeneralPaperPositiveSegmentCompaction (compact count)
set_option autoImplicit false

structure Cache {n m r : ℕ} (G : RationalProportionalGroups n m) (l : RationalSegmentLottery m r) where
  routes : PreparedGroupOutput G
  segments : PreparedSegmentDescriptor (compact l)
  midpointBits : ℕ
  midpointCount : ℕ
  midpointCount_correct : midpointCount = 2 ^ midpointBits
  budget : ℚ

def project {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (p : GeneralPaperEqualPreparedCache.Prepared G l) : Cache G l :=
  ⟨p.routes, p.segments, p.midpointBits, p.midpointCount, p.midpointCount_correct, p.budget⟩

noncomputable def view {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (p : Cache G l) : GeneralPaperEqualPreparedCache.Prepared G l :=
  let D := GeneralPaperEqualCategoricalIntegerData.denominator p.segments.lottery.weight
  ⟨p.routes, p.segments, D, rfl,
    FixedArrayTable.ofFn (GeneralPaperEqualCategoricalIntegerData.count p.segments.lottery.weight),
    FixedArrayTable.read_ofFn _, UniformNatRejection.width D, rfl,
    p.midpointBits, p.midpointCount, p.midpointCount_correct, p.budget⟩

theorem project_view {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (p : Cache G l) : project (view p) = p := rfl

theorem unique {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (a b : Cache G l) (hk : a.midpointBits = b.midpointBits) (hB : a.budget = b.budget) : a = b := by
  have hRoutes : a.routes = b.routes := by
    have h := GeneralPaperNativeQuantizedLabels.table_ext a.routes.table b.routes.table
      (fun j => (a.routes.correct j).trans (b.routes.correct j).symm)
    exact GeneralPaperEqualRouteConstruction.prepared_eq _ _ h
  have hSegments := GeneralPaperSegmentExpressionCompiler.unique a.segments b.segments
  have hCount := a.midpointCount_correct.trans ((congrArg (fun k => 2 ^ k) hk).trans b.midpointCount_correct.symm)
  cases a
  cases b
  cases hRoutes
  cases hSegments
  cases hk
  cases hCount
  cases hB
  rfl

theorem view_project {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (p : GeneralPaperEqualPreparedCache.Prepared G l) : view (project p) = p := by
  cases p with
  | mk routes segments D hD counts hc width hw K N hN B =>
    have he : counts = FixedArrayTable.ofFn (GeneralPaperEqualCategoricalIntegerData.count segments.lottery.weight) :=
      GeneralPaperNativeQuantizedLabels.table_ext _ _
        (fun i => (hc i).trans (FixedArrayTable.read_ofFn _ i).symm)
    subst counts
    subst D
    subst width
    rfl

end Blotto.GeneralPaperEqualRealCache
