import Blotto.GeneralPaperSelectedRank

/-! Materialize all cached query ranks in a native array once per epoch.
The actual quantile-summary ordering discharges the rank-search prerequisite.
Prefix queries then have the exact occurrence correspondence they require.
-/
namespace Blotto.GeneralPaperRankCache
open scoped BigOperators
open GeneralPaperSelectedRank GeneralPaperPreparedPowers GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery
set_option autoImplicit false
set_option maxHeartbeats 3000000

def build {m : ℕ} (k : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (cuts : FixedArrayTable m ℕ) : FixedArrayTable m (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1)) × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun q =>
    let found := lookup k summary (cuts.read q)
    (found.position,found.work+8))

theorem read_build {m : ℕ} (k : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (cuts : FixedArrayTable m ℕ) (q : Fin m) :
    (build k summary cuts).1.read q=(lookup k summary (cuts.read q)).position := by
  rw [build,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]

theorem cached_spec {m : ℕ} (k : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hMono : Monotone summary.read) (cuts : FixedArrayTable m ℕ) (q : Fin m)
    (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    summary.read r<cuts.read q ↔ r.val<((build k summary cuts).1.read q).val := by
  rw [read_build]
  exact lookup_spec k summary hMono (cuts.read q) r

theorem source_summary_spec {m : ℕ} (lambda k height : ℕ) (node : Node height)
    (hHeight : height≤lambda+1) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node)
    (cuts : FixedArrayTable m ℕ) (q : Fin m) (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    let summary := GeneralPaperInitialSummary.build (prepare lambda k) (GeneralPaperQuantileComparison.width lambda k)
      (GeneralPaperSourceParameters.prepare k).summarySize height node
    summary.read r<cuts.read q ↔ r.val<((build k summary cuts).1.read q).val :=
  cached_spec k _ (GeneralPaperSummaryOrdered.summary_ordered lambda k height node hHeight hValid hPath) cuts q r

theorem cached_prefix {m : ℕ} (k : ℕ) (summary values : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hMono : Monotone summary.read) (cuts : FixedArrayTable m ℕ) (q : Fin m) :
    (GeneralPaperEpochPrefixArray.build values).read ((build k summary cuts).1.read q)=
      ∑ r, if summary.read r<cuts.read q then values.read r else 0 :=
  GeneralPaperEpochPrefixQuery.read_location_count values summary.read _ (cuts.read q) (cached_spec k summary hMono cuts q)

theorem build_work {m : ℕ} (k : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (cuts : FixedArrayTable m ℕ) :
    (build k summary cuts).2≤m*((35+k)*(12*(35+k)+34)+66)+18 := by
  have he := Finset.sum_le_sum (fun (q : Fin m) (_ : q∈Finset.univ) =>
    Nat.add_le_add_right (lookup_work k summary (cuts.read q)) 8)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at he
  rw [build,PaperIndexedArrayConstruction.run_work,GeneralPaperEpochLevelArray.overhead]
  nlinarith

end Blotto.GeneralPaperRankCache
