import Blotto.GeneralPaperMeshCountBounds

/-! One four-count query feeds one integer unsigned increment. The callback
annotation formation, branch/record reads and returned scalar are included.
The retained mesh is borrowed instead of rebuilding source parameters.
-/
namespace Blotto.GeneralPaperUnsignedDeltaStepPrice
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshQueryMetadata (referenceWord)
open GeneralPaperMeshPrefixInvariant (Good)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def run {n k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W mesh : ℕ) (response : Bool)
    (cdfPrefix tailPrefix : Prefix k) (plan : GeneralPaperQueryLossCounts.Plan k n) (q : Fin n) : ℕ × ℕ :=
  let counts := GeneralPaperMeshPairExecution.counts bits price W mesh cdfPrefix tailPrefix plan q
  let inc := GeneralPaperIncrementPrice.unsigned price W response mesh counts.1.lower counts.1.upper counts.1.positive counts.1.negative
  (inc.1,counts.2+inc.2+GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) counts.1.work 24+
    96*(if bits then referenceWord W k else W))

theorem data {n k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W mesh : ℕ) (response : Bool)
    (cdfPrefix tailPrefix : Prefix k) (plan : GeneralPaperQueryLossCounts.Plan k n) (q : Fin n)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (run bits price W mesh response cdfPrefix tailPrefix plan q).1=(GeneralPaperQueryLossCounts.step k response cdfPrefix tailPrefix plan q).1 := by
  unfold run GeneralPaperQueryLossCounts.step GeneralPaperQueryLossCounts.increment
  dsimp only
  rw [GeneralPaperIncrementPrice.unsigned_data,GeneralPaperMeshPairExecution.counts_data bits price W mesh _ _ _ _ hMesh,hMesh]

def profile (price : ℕ → ℕ) (W m lambda k Qv : ℕ) : ℕ :=
  GeneralPaperMeshPairPrice.countsProfile price W m lambda k Qv+
    16*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+64*W+96*referenceWord W k

def arithmeticProfile (k : ℕ) : ℕ := GeneralPaperMeshPairPrice.countsArithmeticProfile k+176

theorem bit_work {n k : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda Qv mesh : ℕ) (response : Bool)
    (cdfPrefix tailPrefix : Prefix k) (plan : GeneralPaperQueryLossCounts.Plan k n) (q : Fin n)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hCDF : Good m lambda k Qv cdfPrefix) (hTail : Good m lambda k Qv tailPrefix) :
    (run true price W mesh response cdfPrefix tailPrefix plan q).2≤profile price W m lambda k Qv := by
  let counts := GeneralPaperMeshPairExecution.counts true price W mesh cdfPrefix tailPrefix plan q
  have hq := GeneralPaperMeshPairPrice.counts_bit_work price hMono W m lambda Qv mesh cdfPrefix tailPrefix plan q hMesh hCDF hTail
  have hb := GeneralPaperMeshCountBounds.counts_bound true price W m lambda Qv mesh cdfPrefix tailPrefix plan q hMesh hCDF hTail
  change GeneralPaperQueryLossCounts.Bounds k counts.1 at hb
  have hi := GeneralPaperIncrementPrice.unsigned_work price hMono W m lambda k Qv mesh
    counts.1.lower counts.1.upper counts.1.positive counts.1.negative hMesh
    (hb.1.trans_eq hMesh.symm) (hb.2.1.trans_eq hMesh.symm)
    (hb.2.2.1.trans_eq hMesh.symm) (hb.2.2.2.trans_eq hMesh.symm) response
  have hm := GeneralPaperMeshQueryMetadata.add_work price hMono m lambda k Qv counts.1.work 24 (by
    rw [GeneralPaperMeshPairExecution.counts_data true price W mesh _ _ _ _ hMesh,GeneralPaperQueryLossCounts.evaluate_work]
    unfold GeneralPaperMeshQueryMetadata.cap; omega)
  have h := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hq hi) hm) (96*referenceWord W k)
  exact h.trans_eq (by unfold profile; ring)

theorem arithmetic_work {n k : ℕ} (mesh : ℕ) (response : Bool) (cdfPrefix tailPrefix : Prefix k)
    (plan : GeneralPaperQueryLossCounts.Plan k n) (q : Fin n) :
    (run false (fun _ => 1) 1 mesh response cdfPrefix tailPrefix plan q).2≤arithmeticProfile k := by
  have hq := GeneralPaperMeshPairPrice.counts_arithmetic_work mesh cdfPrefix tailPrefix plan q
  unfold run
  dsimp only
  rw [GeneralPaperIncrementPrice.unsigned_arithmetic]
  change (GeneralPaperMeshPairExecution.counts false (fun _ => 1) 1 mesh cdfPrefix tailPrefix plan q).2+78+2+96≤_
  unfold arithmeticProfile
  omega

end Blotto.GeneralPaperUnsignedDeltaStepPrice
