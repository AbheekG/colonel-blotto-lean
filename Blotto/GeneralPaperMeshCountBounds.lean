import Blotto.GeneralPaperIncrementPrice

/-! Query bounds from retained positive prefix invariants, for arbitrary
cached ranks. These expose the exact count caps needed by integer increment
prices; no rank validation or probability recomputation is executed.
-/
namespace Blotto.GeneralPaperMeshCountBounds
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshPrefixInvariant (Good)
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

theorem prefix_bound {k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W m lambda Qv mesh : ℕ)
    (prefixes : Prefix k) (rank : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hGood : Good m lambda k Qv prefixes) :
    (GeneralPaperCachedMeshPrefixQuery.run bits price W mesh prefixes rank).1.quotient≤mesh := by
  rw [GeneralPaperCachedMeshPrefixQuery.data bits price W mesh _ _ hMesh,hMesh]
  exact (GeneralPaperCDFMesh.selected_bounds k _ _ hGood.1 (hGood.2.1 rank)).1

theorem cached_prefix_bound {n k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W m lambda Qv mesh : ℕ)
    (prefixes : Prefix k) (ranks : FixedArrayTable n (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))) (q : Fin n)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hGood : Good m lambda k Qv prefixes) :
    (GeneralPaperCachedMeshPrefixQuery.cached bits price W mesh prefixes ranks q).1.quotient≤mesh :=
  prefix_bound bits price W m lambda Qv mesh prefixes (ranks.read q) hMesh hGood

theorem interval_bound {k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W m lambda Qv mesh : ℕ)
    (prefixes : Prefix k) (lo hi : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hGood : Good m lambda k Qv prefixes) :
    (GeneralPaperCachedMeshIntervalQuery.run bits price W mesh prefixes lo hi).1.quotient≤mesh := by
  rw [GeneralPaperCachedMeshIntervalQuery.data bits price W mesh _ _ _ hMesh,hMesh]
  exact (GeneralPaperCDFMesh.selected_bounds k _ _ hGood.1 ((Nat.sub_le _ _).trans (hGood.2.1 hi))).1

theorem cached_interval_bound {n k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W m lambda Qv mesh : ℕ)
    (prefixes : Prefix k) (ranks : FixedArrayTable n (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))) (lo hi : Fin n)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hGood : Good m lambda k Qv prefixes) :
    (GeneralPaperCachedMeshIntervalQuery.cached bits price W mesh prefixes ranks lo hi).1.quotient≤mesh :=
  interval_bound bits price W m lambda Qv mesh prefixes (ranks.read lo) (ranks.read hi) hMesh hGood

theorem counts_bound {n k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W m lambda Qv mesh : ℕ)
    (cdfPrefix tailPrefix : Prefix k) (plan : GeneralPaperQueryLossCounts.Plan k n) (q : Fin n)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hCDF : Good m lambda k Qv cdfPrefix) (hTail : Good m lambda k Qv tailPrefix) :
    GeneralPaperQueryLossCounts.Bounds k (GeneralPaperMeshPairExecution.counts bits price W mesh cdfPrefix tailPrefix plan q).1 := by
  have hl := cached_prefix_bound bits price W m lambda Qv mesh cdfPrefix plan.cdf.lower q hMesh hCDF
  have hu := cached_prefix_bound bits price W m lambda Qv mesh cdfPrefix plan.cdf.upper q hMesh hCDF
  have hp := cached_interval_bound bits price W m lambda Qv mesh tailPrefix plan.tails.positive q.castSucc (Fin.last n) hMesh hTail
  have hn := cached_interval_bound bits price W m lambda Qv mesh tailPrefix plan.tails.negative q.castSucc (Fin.last n) hMesh hTail
  rw [hMesh] at hl hu hp hn ⊢
  exact ⟨hl,hu,hp,hn⟩

end Blotto.GeneralPaperMeshCountBounds
