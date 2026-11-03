import Blotto.GeneralPaperStoredCategoricalCounts

/-! The prepared cache consumes actual measured compact segments and integer
data. All loops use stored array sizes. Integer and midpoint-power prices are
retained; full width/control/closure and lifetime joins remain separate. -/
namespace Blotto.GeneralPaperEqualCompactedCache
open GeneralPaperEqualPreparedCache (Prepared)
open GeneralPaperPositiveSegmentCompaction (compact)
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem unique {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (p q : Prepared G l) (hK : p.midpointBits = q.midpointBits) (hB : p.budget = q.budget) : p = q := by
  have hRoutes := GeneralPaperEqualRouteConstruction.prepared_eq p.routes q.routes
    (GeneralPaperNativeQuantizedLabels.table_ext p.routes.table q.routes.table
      (fun j => (p.routes.correct j).trans (q.routes.correct j).symm))
  have hSegments := GeneralPaperSegmentExpressionCompiler.unique p.segments q.segments
  have hD : p.D = q.D := by rw [p.D_correct, q.D_correct, hSegments]
  have hCounts := GeneralPaperNativeQuantizedLabels.table_ext p.counts q.counts (fun i => by
    rw [p.counts_correct, q.counts_correct, hSegments])
  have hRange : p.rangeBits = q.rangeBits := by rw [p.rangeBits_correct, q.rangeBits_correct, hD]
  have hMid : p.midpointCount = q.midpointCount := by rw [p.midpointCount_correct, q.midpointCount_correct, hK]
  cases p
  cases q
  cases hRoutes
  cases hSegments
  cases hD
  cases hCounts
  cases hRange
  cases hK
  cases hMid
  cases hB
  rfl

def make {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (routes : PreparedGroupOutput G) (segments : PreparedSegmentDescriptor (compact l))
    (model : RationalCostModel) (A K : ℕ) (budget : ℚ) : Prepared G l × (ℕ × ℕ × ℕ) :=
  let integer := GeneralPaperStoredCategoricalCounts.run segments model A
  let power := GeneralPaperNatPowerBits.run model.rat A 2 K
  let actual : Prepared G l :=
    ⟨routes, segments, integer.1.D, integer.1.D_correct, integer.1.counts, integer.1.counts_correct,
      UniformNatRejection.width integer.1.D, rfl, K, power.1.power, (by
        rw [GeneralPaperNatPowerBits.data]
        exact (GeneralPaperNatPower.data 2 K).1), budget⟩
  (actual, (integer.2.1, integer.2.2, power.2 + 128 * A + 128))

theorem make_data {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (routes : PreparedGroupOutput G) (segments : PreparedSegmentDescriptor (compact l))
    (model : RationalCostModel) (A K : ℕ) (budget : ℚ) :
    (make routes segments model A K budget).1 = GeneralPaperEqualPreparedCache.prepare G l K budget :=
  unique _ _ rfl rfl

def run {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (routes : PreparedGroupOutput G) (full : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A K : ℕ) (budget : ℚ) : Prepared G l × (ℕ × ℕ × ℕ × ℕ) :=
  let compacted := GeneralPaperPreparedSegmentCompaction.run full model A
  let actual := make routes compacted.1 model A K budget
  (actual.1, (compacted.2, actual.2.1, actual.2.2.1, actual.2.2.2))

theorem data {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (routes : PreparedGroupOutput G) (full : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A K : ℕ) (budget : ℚ) :
    (run routes full model A K budget).1 = GeneralPaperEqualPreparedCache.prepare G l K budget := by
  unfold run
  dsimp only
  exact make_data routes _ model A K budget

end Blotto.GeneralPaperEqualCompactedCache
