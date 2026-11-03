import Blotto.GeneralPaperUnsignedDeltaStepPrice

/-! Signed updates borrow one cached CDF count, compare the actual code and
selected bid, form one integer increment and retain the complete native
result. Full code words stay separate from the shorter mesh-counter words.
-/
namespace Blotto.GeneralPaperSignedDeltaStepPrice
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperMeshQueryMetadata (referenceWord)
open GeneralPaperMeshPrefixInvariant (Good)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def run {n k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W mesh U bid : ℕ) (prefixes : Prefix k)
    (plan : GeneralPaperSignedUpdatePlan.Plan k n) (q : Fin n) : GeneralPaperSignedUpdatePlan.Result × ℕ :=
  let queried := GeneralPaperCachedMeshPrefixQuery.cached bits price W mesh prefixes plan.ranks q
  let code := plan.codes.read q
  let position := plan.positions.read q
  let positive := decide (code<U)
  let hit := decide (bid≤position)
  let inc := GeneralPaperIncrementPrice.signed price W mesh queried.1.quotient positive hit
  (⟨inc.1,queried.1.quotient,positive,hit,queried.1.work+24⟩,
    queried.2+inc.2+GeneralPaperIntegerWordPrice.compare price code U+
      GeneralPaperIntegerWordPrice.compare price bid position+
      GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) queried.1.work 24+
      128*(if bits then referenceWord W k else W))

theorem data {n k : ℕ} (bits : Bool) (price : ℕ → ℕ) (W mesh U bid : ℕ) (prefixes : Prefix k)
    (plan : GeneralPaperSignedUpdatePlan.Plan k n) (q : Fin n)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (run bits price W mesh U bid prefixes plan q).1=GeneralPaperSignedUpdatePlan.evaluate k U bid prefixes plan q := by
  unfold run GeneralPaperSignedUpdatePlan.evaluate
  dsimp only
  rw [GeneralPaperIncrementPrice.signed_data,GeneralPaperCachedMeshPrefixQuery.cached_data bits price W mesh _ _ _ hMesh,hMesh]

theorem code_word (lambda n : ℕ) (hn : n≤2^(lambda+1)) :
    1+binaryWordWidth n≤GeneralPaperDecoderControls.operandWidth lambda := by
  have h := (binaryWordWidth_mono hn).trans (GeneralPaperNatPowerOperands.power_width 2 (lambda+1))
  have h2 : binaryWordWidth 2=2 := by decide
  rw [h2] at h
  unfold GeneralPaperDecoderControls.operandWidth
  omega

def profile (price : ℕ → ℕ) (W m lambda k Qv : ℕ) : ℕ :=
  GeneralPaperCachedMeshPrefixQuery.cachedProfile price W m lambda k Qv+
    12*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+
    2*price (GeneralPaperDecoderControls.operandWidth lambda)+64*W+128*referenceWord W k

def arithmeticProfile (k : ℕ) : ℕ := GeneralPaperCachedMeshPrefixQuery.cachedArithmeticProfile k+206

theorem bit_work {n k : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda Qv mesh U bid : ℕ)
    (prefixes : Prefix k) (plan : GeneralPaperSignedUpdatePlan.Plan k n) (q : Fin n)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hGood : Good m lambda k Qv prefixes)
    (hU : U≤2^(lambda+1)) (hBid : bid≤2^(lambda+1))
    (hCode : plan.codes.read q≤2^(lambda+1)) (hPosition : plan.positions.read q≤2^(lambda+1)) :
    (run true price W mesh U bid prefixes plan q).2≤profile price W m lambda k Qv := by
  let queried := GeneralPaperCachedMeshPrefixQuery.cached true price W mesh prefixes plan.ranks q
  have hq := GeneralPaperCachedMeshPrefixQuery.cached_bit_work price hMono W m lambda Qv mesh prefixes plan.ranks q hMesh hGood
  have hb := GeneralPaperMeshCountBounds.cached_prefix_bound true price W m lambda Qv mesh prefixes plan.ranks q hMesh hGood
  have hi := GeneralPaperIncrementPrice.signed_work price hMono W m lambda k Qv mesh queried.1.quotient hMesh hb
    (decide (plan.codes.read q<U)) (decide (bid≤plan.positions.read q))
  have hc := GeneralPaperIntegerWordPrice.compare_le price hMono _ _ _ (code_word lambda _ hCode) (code_word lambda _ hU)
  have hp := GeneralPaperIntegerWordPrice.compare_le price hMono _ _ _ (code_word lambda _ hBid) (code_word lambda _ hPosition)
  have hm := GeneralPaperMeshQueryMetadata.add_work price hMono m lambda k Qv queried.1.work 24 (by
    rw [GeneralPaperCachedMeshPrefixQuery.cached_data true price W mesh _ _ _ hMesh,GeneralPaperRankedCDFQuery.cached_work]
    unfold GeneralPaperMeshQueryMetadata.cap; omega)
  have h := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hq hi) hc) hp) hm) (128*referenceWord W k)
  exact h.trans_eq (by unfold profile; ring)

theorem arithmetic_work {n k : ℕ} (mesh U bid : ℕ) (prefixes : Prefix k)
    (plan : GeneralPaperSignedUpdatePlan.Plan k n) (q : Fin n) :
    (run false (fun _ => 1) 1 mesh U bid prefixes plan q).2≤arithmeticProfile k := by
  have hq := GeneralPaperCachedMeshPrefixQuery.cached_arithmetic_work mesh prefixes plan.ranks q
  unfold run
  dsimp only
  rw [GeneralPaperIncrementPrice.signed_arithmetic]
  change (GeneralPaperCachedMeshPrefixQuery.cached false (fun _ => 1) 1 mesh prefixes plan.ranks q).2+74+1+1+2+128≤_
  unfold arithmeticProfile
  omega

end Blotto.GeneralPaperSignedDeltaStepPrice
