import Blotto.GeneralPaperCachedMeshPrefixQuery

/-! Two cached ranks select one exact integer prefix difference, which is
rounded once against the whole-block total. Both metadata layers and every
prefix/rank read, subtraction and constructed-depth operation are included.
-/
namespace Blotto.GeneralPaperCachedMeshIntervalQuery
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshQueryMetadata (referenceWord)
open GeneralPaperMeshPrefixInvariant (Good)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def run {k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W mesh : ℕ) (prefixes : Prefix k)
    (lo hi : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1)) : GeneralPaperBoundedQuotient.Result × ℕ :=
  let high := prefixes.read hi
  let low := prefixes.read lo
  let numerator := high-low
  let queried := GeneralPaperMeshQueryExecution.selected price W k mesh numerator
    (prefixes.read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize))
  (⟨queried.1.quotient,queried.1.remainder,queried.1.work+24⟩,
    queried.2+GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a-b) high low+
      GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) queried.1.work 24+
      96*(if bits then referenceWord W k else W))

def cached {n k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W mesh : ℕ) (prefixes : Prefix k)
    (ranks : FixedArrayTable n (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))) (lo hi : Fin n) :
    GeneralPaperBoundedQuotient.Result × ℕ :=
  let queried := run bits price W mesh prefixes (ranks.read lo) (ranks.read hi)
  (⟨queried.1.quotient,queried.1.remainder,queried.1.work+16⟩,
    queried.2+GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) queried.1.work 16+
      64*(if bits then referenceWord W k else W))

theorem data {k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W mesh : ℕ) (prefixes : Prefix k)
    (lo hi : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (run bits price W mesh prefixes lo hi).1=GeneralPaperIntervalQuery.evaluate k prefixes lo hi := by
  unfold run GeneralPaperIntervalQuery.evaluate GeneralPaperPrefixInterval.numerator
  dsimp only
  rw [GeneralPaperMeshQueryExecution.selected_data price W k mesh _ _ hMesh]

theorem cached_data {n k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W mesh : ℕ) (prefixes : Prefix k)
    (ranks : FixedArrayTable n (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))) (lo hi : Fin n)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (cached bits price W mesh prefixes ranks lo hi).1=GeneralPaperIntervalQuery.cached k prefixes ranks lo hi := by
  unfold cached GeneralPaperIntervalQuery.cached
  dsimp only
  rw [data bits price W mesh _ _ _ hMesh]

def profile (price : ℕ → ℕ) (W m lambda k Qv : ℕ) : ℕ :=
  GeneralPaperMeshQueryEnvelope.profile price W m lambda k Qv+
    4*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+96*referenceWord W k

def cachedProfile (price : ℕ → ℕ) (W m lambda k Qv : ℕ) : ℕ :=
  profile price W m lambda k Qv+2*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+64*referenceWord W k

def arithmeticProfile (k : ℕ) : ℕ := GeneralPaperMeshQueryEnvelope.arithmeticProfile k+100
def cachedArithmeticProfile (k : ℕ) : ℕ := arithmeticProfile k+66

theorem bit_work {k : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda Qv mesh : ℕ)
    (prefixes : Prefix k) (lo hi : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hGood : Good m lambda k Qv prefixes) :
    (run true price W mesh prefixes lo hi).2≤profile price W m lambda k Qv := by
  let numerator := prefixes.read hi-prefixes.read lo
  have hn : numerator≤prefixes.read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize) :=
    (Nat.sub_le _ _).trans (hGood.2.1 hi)
  have hq := GeneralPaperMeshQueryEnvelope.selected_work price hMono W m lambda k Qv mesh numerator _
    hMesh hGood.1 hn hGood.2.2
  have hs := GeneralPaperMeshPrefixInvariant.difference_work price hMono m lambda k Qv prefixes hGood lo hi
  have hm := GeneralPaperMeshQueryMetadata.selected_add_work price hMono m lambda k Qv numerator
    (prefixes.read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize)) 24 (by omega)
  rw [←GeneralPaperMeshQueryExecution.selected_data price W k mesh _ _ hMesh] at hm
  have h := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hq hs) hm) (96*referenceWord W k)
  exact h.trans_eq (by unfold profile; ring)

theorem cached_bit_work {n k : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda Qv mesh : ℕ)
    (prefixes : Prefix k) (ranks : FixedArrayTable n (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))) (lo hi : Fin n)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hGood : Good m lambda k Qv prefixes) :
    (cached true price W mesh prefixes ranks lo hi).2≤cachedProfile price W m lambda k Qv := by
  have hq := bit_work price hMono W m lambda Qv mesh prefixes (ranks.read lo) (ranks.read hi) hMesh hGood
  have hm := GeneralPaperMeshQueryMetadata.add_work price hMono m lambda k Qv
    (run true price W mesh prefixes (ranks.read lo) (ranks.read hi)).1.work 16 (by
      rw [data true price W mesh _ _ _ hMesh,GeneralPaperIntervalQuery.evaluate_work]
      unfold GeneralPaperMeshQueryMetadata.cap; omega)
  exact Nat.add_le_add_right (Nat.add_le_add hq hm) _

theorem arithmetic_work {k : ℕ} (mesh : ℕ) (prefixes : Prefix k)
    (lo hi : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1)) :
    (run false (fun _ => 1) 1 mesh prefixes lo hi).2≤arithmeticProfile k := by
  have hq := GeneralPaperMeshQueryWork.selected_arithmetic_work k mesh (prefixes.read hi-prefixes.read lo)
    (prefixes.read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize))
  change (GeneralPaperMeshQueryExecution.selected (fun _ => 1) 1 k mesh (prefixes.read hi-prefixes.read lo)
    (prefixes.read (Fin.last (GeneralPaperSourceParameters.prepare k).summarySize))).2+2+2+96≤_
  unfold arithmeticProfile GeneralPaperMeshQueryEnvelope.arithmeticProfile
  omega

theorem cached_arithmetic_work {n k : ℕ} (mesh : ℕ) (prefixes : Prefix k)
    (ranks : FixedArrayTable n (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))) (lo hi : Fin n) :
    (cached false (fun _ => 1) 1 mesh prefixes ranks lo hi).2≤cachedArithmeticProfile k := by
  have hq := arithmetic_work mesh prefixes (ranks.read lo) (ranks.read hi)
  change (run false (fun _ => 1) 1 mesh prefixes (ranks.read lo) (ranks.read hi)).2+2+64≤_
  unfold cachedArithmeticProfile
  omega

theorem same_data {n k : ℕ} (price : ℕ → ℕ) (W mesh : ℕ) (prefixes : Prefix k)
    (ranks : FixedArrayTable n (Fin ((GeneralPaperSourceParameters.prepare k).summarySize+1))) (lo hi : Fin n)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (cached true price W mesh prefixes ranks lo hi).1=(cached false (fun _ => 1) 1 mesh prefixes ranks lo hi).1 := by
  rw [cached_data true price W mesh _ _ _ _ hMesh,cached_data false (fun _ => 1) 1 mesh _ _ _ _ hMesh]

end Blotto.GeneralPaperCachedMeshIntervalQuery
