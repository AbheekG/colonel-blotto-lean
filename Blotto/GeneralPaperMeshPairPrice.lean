import Blotto.GeneralPaperMeshPairExecution

/-! Both native query pairs and their four-count composition have complete
model prices. Retained records derive every annotation cap; the two prefix
invariants are supplied by the same reached pre-update snapshot.
-/
namespace Blotto.GeneralPaperMeshPairPrice
open GeneralPaperMeshPairExecution
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshQueryMetadata (referenceWord)
open GeneralPaperMeshPrefixInvariant (Good)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def cdfProfile (price : ℕ → ℕ) (W m lambda k Qv : ℕ) : ℕ :=
  2*GeneralPaperCachedMeshPrefixQuery.cachedProfile price W m lambda k Qv+
    4*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+96*referenceWord W k

def tailsProfile (price : ℕ → ℕ) (W m lambda k Qv : ℕ) : ℕ :=
  2*GeneralPaperCachedMeshIntervalQuery.cachedProfile price W m lambda k Qv+
    4*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+96*referenceWord W k

def countsProfile (price : ℕ → ℕ) (W m lambda k Qv : ℕ) : ℕ :=
  cdfProfile price W m lambda k Qv+tailsProfile price W m lambda k Qv+
    4*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+96*referenceWord W k

def cdfArithmeticProfile (k : ℕ) : ℕ := 2*GeneralPaperCachedMeshPrefixQuery.cachedArithmeticProfile k+100
def tailsArithmeticProfile (k : ℕ) : ℕ := 2*GeneralPaperCachedMeshIntervalQuery.cachedArithmeticProfile k+100
def countsArithmeticProfile (k : ℕ) : ℕ := cdfArithmeticProfile k+tailsArithmeticProfile k+100

theorem metadata_work (price : ℕ → ℕ) (hMono : Monotone price) (m lambda k Qv a b constant : ℕ)
    (hSum : a+b+constant≤GeneralPaperMeshQueryMetadata.cap k) :
    GeneralPaperPowerTableBounds.metadataCost price a b constant≤4*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) :=
  GeneralPaperPowerTableBounds.metadata_work price hMono a b constant _ _ hSum
    (GeneralPaperMeshQueryMetadata.operand_word m lambda k Qv)

theorem pair_combine (a b c C M E : ℕ) (ha : a≤C) (hb : b≤C) (hc : c≤M) : a+b+c+E≤2*C+M+E := by omega

theorem cdf_bit_work {n k : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda Qv mesh : ℕ)
    (prefixes : Prefix k) (plan : GeneralPaperCDFPairPlan.Plan k n) (q : Fin n)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hGood : Good m lambda k Qv prefixes) :
    (cdf true price W mesh prefixes plan q).2≤cdfProfile price W m lambda k Qv := by
  have hl := GeneralPaperCachedMeshPrefixQuery.cached_bit_work price hMono W m lambda Qv mesh prefixes plan.lower q hMesh hGood
  have hu := GeneralPaperCachedMeshPrefixQuery.cached_bit_work price hMono W m lambda Qv mesh prefixes plan.upper q hMesh hGood
  have hm := metadata_work price hMono m lambda k Qv
    (GeneralPaperCachedMeshPrefixQuery.cached true price W mesh prefixes plan.lower q).1.work
    (GeneralPaperCachedMeshPrefixQuery.cached true price W mesh prefixes plan.upper q).1.work 8 (by
      rw [GeneralPaperCachedMeshPrefixQuery.cached_data true price W mesh _ _ _ hMesh,
        GeneralPaperCachedMeshPrefixQuery.cached_data true price W mesh _ _ _ hMesh,
        GeneralPaperRankedCDFQuery.cached_work,GeneralPaperRankedCDFQuery.cached_work]
      unfold GeneralPaperMeshQueryMetadata.cap; omega)
  exact pair_combine _ _ _ _ _ _ hl hu hm

theorem tails_bit_work {n k : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda Qv mesh : ℕ)
    (prefixes : Prefix k) (plan : GeneralPaperSignedTailPlan.Plan k n) (q : Fin n)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hGood : Good m lambda k Qv prefixes) :
    (tails true price W mesh prefixes plan q).2≤tailsProfile price W m lambda k Qv := by
  have hp := GeneralPaperCachedMeshIntervalQuery.cached_bit_work price hMono W m lambda Qv mesh prefixes plan.positive q.castSucc (Fin.last n) hMesh hGood
  have hn := GeneralPaperCachedMeshIntervalQuery.cached_bit_work price hMono W m lambda Qv mesh prefixes plan.negative q.castSucc (Fin.last n) hMesh hGood
  have hm := metadata_work price hMono m lambda k Qv
    (GeneralPaperCachedMeshIntervalQuery.cached true price W mesh prefixes plan.positive q.castSucc (Fin.last n)).1.work
    (GeneralPaperCachedMeshIntervalQuery.cached true price W mesh prefixes plan.negative q.castSucc (Fin.last n)).1.work 8 (by
      rw [GeneralPaperCachedMeshIntervalQuery.cached_data true price W mesh _ _ _ _ hMesh,
        GeneralPaperCachedMeshIntervalQuery.cached_data true price W mesh _ _ _ _ hMesh,
        GeneralPaperIntervalQuery.cached_work,GeneralPaperIntervalQuery.cached_work]
      unfold GeneralPaperMeshQueryMetadata.cap; omega)
  exact pair_combine _ _ _ _ _ _ hp hn hm

theorem counts_bit_work {n k : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda Qv mesh : ℕ)
    (cdfPrefix tailPrefix : Prefix k) (plan : GeneralPaperQueryLossCounts.Plan k n) (q : Fin n)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hCDF : Good m lambda k Qv cdfPrefix) (hTail : Good m lambda k Qv tailPrefix) :
    (counts true price W mesh cdfPrefix tailPrefix plan q).2≤countsProfile price W m lambda k Qv := by
  have hc := cdf_bit_work price hMono W m lambda Qv mesh cdfPrefix plan.cdf q hMesh hCDF
  have ht := tails_bit_work price hMono W m lambda Qv mesh tailPrefix plan.tails q hMesh hTail
  have hm := metadata_work price hMono m lambda k Qv
    (cdf true price W mesh cdfPrefix plan.cdf q).1.work (tails true price W mesh tailPrefix plan.tails q).1.work 16 (by
      rw [cdf_data true price W mesh _ _ _ hMesh,tails_data true price W mesh _ _ _ hMesh,
        GeneralPaperCDFPairPlan.evaluate_work,GeneralPaperSignedTailPlan.evaluate_work]
      unfold GeneralPaperMeshQueryMetadata.cap; omega)
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hc ht) hm) _

theorem metadata_arithmetic (a b constant : ℕ) :
    GeneralPaperPowerTableBounds.metadataCost (fun _ => 1) a b constant=4 := rfl

theorem cdf_arithmetic_work {n k : ℕ} (mesh : ℕ) (prefixes : Prefix k) (plan : GeneralPaperCDFPairPlan.Plan k n) (q : Fin n) :
    (cdf false (fun _ => 1) 1 mesh prefixes plan q).2≤cdfArithmeticProfile k := by
  have hl := GeneralPaperCachedMeshPrefixQuery.cached_arithmetic_work mesh prefixes plan.lower q
  have hu := GeneralPaperCachedMeshPrefixQuery.cached_arithmetic_work mesh prefixes plan.upper q
  have hm := metadata_arithmetic
    (GeneralPaperCachedMeshPrefixQuery.cached false (fun _ => 1) 1 mesh prefixes plan.lower q).1.work
    (GeneralPaperCachedMeshPrefixQuery.cached false (fun _ => 1) 1 mesh prefixes plan.upper q).1.work 8
  change _≤2*GeneralPaperCachedMeshPrefixQuery.cachedArithmeticProfile k+100
  unfold cdf
  dsimp only
  rw [hm]
  simp only [Bool.false_eq_true,ite_false,Nat.mul_one]
  omega

theorem tails_arithmetic_work {n k : ℕ} (mesh : ℕ) (prefixes : Prefix k) (plan : GeneralPaperSignedTailPlan.Plan k n) (q : Fin n) :
    (tails false (fun _ => 1) 1 mesh prefixes plan q).2≤tailsArithmeticProfile k := by
  have hp := GeneralPaperCachedMeshIntervalQuery.cached_arithmetic_work mesh prefixes plan.positive q.castSucc (Fin.last n)
  have hn := GeneralPaperCachedMeshIntervalQuery.cached_arithmetic_work mesh prefixes plan.negative q.castSucc (Fin.last n)
  change _≤2*GeneralPaperCachedMeshIntervalQuery.cachedArithmeticProfile k+100
  unfold tails
  dsimp only
  rw [metadata_arithmetic]
  simp only [Bool.false_eq_true,ite_false,Nat.mul_one]
  omega

theorem counts_arithmetic_work {n k : ℕ} (mesh : ℕ) (cdfPrefix tailPrefix : Prefix k) (plan : GeneralPaperQueryLossCounts.Plan k n) (q : Fin n) :
    (counts false (fun _ => 1) 1 mesh cdfPrefix tailPrefix plan q).2≤countsArithmeticProfile k := by
  have hc := cdf_arithmetic_work mesh cdfPrefix plan.cdf q
  have ht := tails_arithmetic_work mesh tailPrefix plan.tails q
  unfold counts countsArithmeticProfile
  dsimp only
  rw [metadata_arithmetic]
  simp only [Bool.false_eq_true,ite_false,Nat.mul_one]
  omega

end Blotto.GeneralPaperMeshPairPrice
