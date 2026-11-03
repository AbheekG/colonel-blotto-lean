import Blotto.GeneralPaperActualMeshQueryPrice

/-! Strict/weak CDF and positive/negative interval queries share retained
prefixes. Four-count loss queries compose these two pairs once. Complete
native records and all metadata additions are preserved and priced.
-/
namespace Blotto.GeneralPaperMeshPairExecution
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshQueryMetadata (referenceWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def cdf {n k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W mesh : ℕ) (prefixes : Prefix k)
    (plan : GeneralPaperCDFPairPlan.Plan k n) (q : Fin n) : GeneralPaperCDFPairPlan.Pair × ℕ :=
  let lower := GeneralPaperCachedMeshPrefixQuery.cached bits price W mesh prefixes plan.lower q
  let upper := GeneralPaperCachedMeshPrefixQuery.cached bits price W mesh prefixes plan.upper q
  (⟨lower.1.quotient,upper.1.quotient,lower.1.work+upper.1.work+8⟩,
    lower.2+upper.2+GeneralPaperPowerTableBounds.metadataCost price lower.1.work upper.1.work 8+
      96*(if bits then referenceWord W k else W))

def tails {n k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W mesh : ℕ) (prefixes : Prefix k)
    (plan : GeneralPaperSignedTailPlan.Plan k n) (q : Fin n) : GeneralPaperSignedTailPlan.Pair × ℕ :=
  let positive := GeneralPaperCachedMeshIntervalQuery.cached bits price W mesh prefixes plan.positive q.castSucc (Fin.last n)
  let negative := GeneralPaperCachedMeshIntervalQuery.cached bits price W mesh prefixes plan.negative q.castSucc (Fin.last n)
  (⟨positive.1.quotient,negative.1.quotient,positive.1.work+negative.1.work+8⟩,
    positive.2+negative.2+GeneralPaperPowerTableBounds.metadataCost price positive.1.work negative.1.work 8+
      96*(if bits then referenceWord W k else W))

def counts {n k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W mesh : ℕ) (cdfPrefix tailPrefix : Prefix k)
    (plan : GeneralPaperQueryLossCounts.Plan k n) (q : Fin n) : GeneralPaperQueryLossCounts.Counts × ℕ :=
  let cp := cdf bits price W mesh cdfPrefix plan.cdf q
  let tp := tails bits price W mesh tailPrefix plan.tails q
  (⟨cp.1.lower,cp.1.upper,tp.1.positive,tp.1.negative,cp.1.work+tp.1.work+16⟩,
    cp.2+tp.2+GeneralPaperPowerTableBounds.metadataCost price cp.1.work tp.1.work 16+
      96*(if bits then referenceWord W k else W))

theorem cdf_data {n k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W mesh : ℕ) (prefixes : Prefix k)
    (plan : GeneralPaperCDFPairPlan.Plan k n) (q : Fin n)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (cdf bits price W mesh prefixes plan q).1=GeneralPaperCDFPairPlan.evaluate k prefixes plan q := by
  unfold cdf GeneralPaperCDFPairPlan.evaluate
  dsimp only
  rw [GeneralPaperCachedMeshPrefixQuery.cached_data bits price W mesh _ _ _ hMesh,
    GeneralPaperCachedMeshPrefixQuery.cached_data bits price W mesh _ _ _ hMesh]

theorem tails_data {n k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W mesh : ℕ) (prefixes : Prefix k)
    (plan : GeneralPaperSignedTailPlan.Plan k n) (q : Fin n)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (tails bits price W mesh prefixes plan q).1=GeneralPaperSignedTailPlan.evaluate k prefixes plan q := by
  unfold tails GeneralPaperSignedTailPlan.evaluate
  dsimp only
  rw [GeneralPaperCachedMeshIntervalQuery.cached_data bits price W mesh _ _ _ _ hMesh,
    GeneralPaperCachedMeshIntervalQuery.cached_data bits price W mesh _ _ _ _ hMesh]

theorem counts_data {n k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W mesh : ℕ) (cdfPrefix tailPrefix : Prefix k)
    (plan : GeneralPaperQueryLossCounts.Plan k n) (q : Fin n)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (counts bits price W mesh cdfPrefix tailPrefix plan q).1=GeneralPaperQueryLossCounts.evaluate k cdfPrefix tailPrefix plan q := by
  unfold counts GeneralPaperQueryLossCounts.evaluate
  dsimp only
  rw [cdf_data bits price W mesh _ _ _ hMesh,tails_data bits price W mesh _ _ _ hMesh]

end Blotto.GeneralPaperMeshPairExecution
