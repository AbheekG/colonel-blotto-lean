import Blotto.GeneralPaperMeshPrefixInvariant

/-! Cached point-CDF queries read one stored rank and two prefix entries.
Every native annotation addition is charged. Rank/reference words and exact
whole-block denominators are retained; no summary or prefix scan executes.
-/
namespace Blotto.GeneralPaperCachedMeshPrefixQuery
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshQueryMetadata (referenceWord)
open GeneralPaperMeshPrefixInvariant (Good)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def run {k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W mesh : ℕ) (prefixes : Prefix k)
    (rank : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1)) : GeneralPaperBoundedQuotient.Result × ℕ :=
  let queried := GeneralPaperMeshQueryExecution.selected price W k mesh (prefixes.read rank)
    (prefixes.read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize))
  (⟨queried.1.quotient,queried.1.remainder,queried.1.work+16⟩,
    queried.2+GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) queried.1.work 16+
      96*(if bits then referenceWord W k else W))

def cached {n k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W mesh : ℕ) (prefixes : Prefix k)
    (ranks : FixedArrayTable n (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))) (q : Fin n) :
    GeneralPaperBoundedQuotient.Result × ℕ :=
  let queried := run bits price W mesh prefixes (ranks.read q)
  (⟨queried.1.quotient,queried.1.remainder,queried.1.work+8⟩,
    queried.2+GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) queried.1.work 8+
      64*(if bits then referenceWord W k else W))

theorem data {k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W mesh : ℕ) (prefixes : Prefix k)
    (rank : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (run bits price W mesh prefixes rank).1=GeneralPaperEpochPrefixQuery.query k prefixes rank := by
  unfold run GeneralPaperEpochPrefixQuery.query
  dsimp only
  rw [GeneralPaperMeshQueryExecution.selected_data price W k mesh _ _ hMesh]

theorem cached_data {n k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W mesh : ℕ) (prefixes : Prefix k)
    (ranks : FixedArrayTable n (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))) (q : Fin n)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (cached bits price W mesh prefixes ranks q).1=GeneralPaperRankedCDFQuery.cached k prefixes ranks q := by
  unfold cached GeneralPaperRankedCDFQuery.cached
  dsimp only
  rw [data bits price W mesh _ _ hMesh]

def profile (price : ℕ → ℕ) (W m lambda k Qv : ℕ) : ℕ :=
  GeneralPaperMeshQueryEnvelope.profile price W m lambda k Qv+
    2*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+96*referenceWord W k

def cachedProfile (price : ℕ → ℕ) (W m lambda k Qv : ℕ) : ℕ :=
  profile price W m lambda k Qv+2*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+64*referenceWord W k

def arithmeticProfile (k : ℕ) : ℕ := GeneralPaperMeshQueryEnvelope.arithmeticProfile k+98
def cachedArithmeticProfile (k : ℕ) : ℕ := arithmeticProfile k+66

theorem bit_work {k : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda Qv mesh : ℕ)
    (prefixes : Prefix k) (rank : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hGood : Good m lambda k Qv prefixes) :
    (run true price W mesh prefixes rank).2≤profile price W m lambda k Qv := by
  have hq := GeneralPaperMeshQueryEnvelope.selected_work price hMono W m lambda k Qv mesh _ _
    hMesh hGood.1 (hGood.2.1 rank) hGood.2.2
  have hm := GeneralPaperMeshQueryMetadata.selected_add_work price hMono m lambda k Qv
    (prefixes.read rank) (prefixes.read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize)) 16 (by omega)
  rw [←GeneralPaperMeshQueryExecution.selected_data price W k mesh _ _ hMesh] at hm
  exact Nat.add_le_add_right (Nat.add_le_add hq hm) _

theorem cached_bit_work {n k : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda Qv mesh : ℕ)
    (prefixes : Prefix k) (ranks : FixedArrayTable n (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))) (q : Fin n)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hGood : Good m lambda k Qv prefixes) :
    (cached true price W mesh prefixes ranks q).2≤cachedProfile price W m lambda k Qv := by
  have hq := bit_work price hMono W m lambda Qv mesh prefixes (ranks.read q) hMesh hGood
  have hm := GeneralPaperMeshQueryMetadata.add_work price hMono m lambda k Qv
    (run true price W mesh prefixes (ranks.read q)).1.work 8 (by
      rw [data true price W mesh _ _ hMesh,GeneralPaperEpochPrefixQuery.query_work]
      unfold GeneralPaperMeshQueryMetadata.cap; omega)
  exact Nat.add_le_add_right (Nat.add_le_add hq hm) _

theorem arithmetic_work {k : ℕ} (mesh : ℕ) (prefixes : Prefix k)
    (rank : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1)) :
    (run false (fun _ => 1) 1 mesh prefixes rank).2≤arithmeticProfile k := by
  have hq := GeneralPaperMeshQueryWork.selected_arithmetic_work k mesh (prefixes.read rank)
    (prefixes.read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize))
  change (GeneralPaperMeshQueryExecution.selected (fun _ => 1) 1 k mesh (prefixes.read rank)
    (prefixes.read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize))).2+2+96≤_
  unfold arithmeticProfile GeneralPaperMeshQueryEnvelope.arithmeticProfile
  omega

theorem cached_arithmetic_work {n k : ℕ} (mesh : ℕ) (prefixes : Prefix k)
    (ranks : FixedArrayTable n (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))) (q : Fin n) :
    (cached false (fun _ => 1) 1 mesh prefixes ranks q).2≤cachedArithmeticProfile k := by
  have hq := arithmetic_work mesh prefixes (ranks.read q)
  change (run false (fun _ => 1) 1 mesh prefixes (ranks.read q)).2+2+64≤_
  unfold cachedArithmeticProfile
  omega

theorem same_data {n k : ℕ} (price : ℕ → ℕ) (W mesh : ℕ) (prefixes : Prefix k)
    (ranks : FixedArrayTable n (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))) (q : Fin n)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (cached true price W mesh prefixes ranks q).1=(cached false (fun _ => 1) 1 mesh prefixes ranks q).1 := by
  rw [cached_data true price W mesh _ _ _ hMesh,cached_data false (fun _ => 1) 1 mesh _ _ _ hMesh]

end Blotto.GeneralPaperCachedMeshPrefixQuery
