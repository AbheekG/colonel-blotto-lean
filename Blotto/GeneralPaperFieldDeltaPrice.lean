import Blotto.GeneralPaperFieldDeltaExecution

/-! Complete prices for all eight arrays, with one retained plan/snapshot
and selected pair of row bids. Uniform array-length bounds are supplied by
the actual cache descriptors in the caller, never by an executed census.
-/
namespace Blotto.GeneralPaperFieldDeltaPrice
open GeneralPaperFieldDeltaExecution
open GeneralPaperEpochFieldState GeneralPaperEpochSnapshot GeneralPaperEpochDeltas
open GeneralPaperEpochFieldAdvancePrice (total total_mono)
open GeneralPaperCatalogueOccurrenceHistory (Learner block)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def profile {k : ℕ} (price : ℕ → ℕ) (W m lambda Qv : ℕ) (state : State k) : ℕ :=
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  let U := GeneralPaperDeltaArrayPrice.unsignedProfile price W m lambda k Qv
  let S := GeneralPaperDeltaArrayPrice.signedProfile price W m lambda k Qv
  total (U s) (U s) (S s) (S s) (U state.plan.pCells.partition.count) (U state.plan.qCells.partition.count)
    (S state.plan.lambdaCells.partition.count) (S state.plan.muCells.partition.count)+256*W

def arithmeticProfile {k : ℕ} (state : State k) : ℕ :=
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  let U := fun n => GeneralPaperDeltaArrayPrice.unsignedArithmeticProfile n k
  let S := fun n => GeneralPaperDeltaArrayPrice.signedArithmeticProfile n k
  total (U s) (U s) (S s) (S s) (U state.plan.pCells.partition.count) (U state.plan.qCells.partition.count)
    (S state.plan.lambdaCells.partition.count) (S state.plan.muCells.partition.count)+256

def uniformProfile (price : ℕ → ℕ) (W m lambda k Qv B : ℕ) : ℕ :=
  4*GeneralPaperDeltaArrayPrice.unsignedProfile price W m lambda k Qv B+
    4*GeneralPaperDeltaArrayPrice.signedProfile price W m lambda k Qv B+256*W

def uniformArithmeticProfile (k B : ℕ) : ℕ :=
  4*GeneralPaperDeltaArrayPrice.unsignedArithmeticProfile B k+4*GeneralPaperDeltaArrayPrice.signedArithmeticProfile B k+256

theorem bit_work {k : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda Qv mesh : ℕ)
    (state : State k) (snapshot : Snapshot k) (choice : Choice state.plan)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hGood : ∀ learner,GeneralPaperMeshPrefixInvariant.Good m lambda k Qv (block learner snapshot).cdf)
    (hSafe : GeneralPaperDeltaPlanBounds.PlanSafe lambda state.plan) :
    (run true (fun w => w) price W mesh state snapshot choice).2≤profile price W m lambda Qv state := by
  exact Nat.add_le_add_right (total_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (GeneralPaperDeltaArrayPrice.unsigned_bit_work price hMono W m lambda Qv mesh false _ _ _ hMesh (hGood .q) (hGood .lambda))
    (GeneralPaperDeltaArrayPrice.unsigned_bit_work price hMono W m lambda Qv mesh true _ _ _ hMesh (hGood .p) (hGood .mu))
    (GeneralPaperDeltaArrayPrice.signed_bit_work price hMono W m lambda Qv mesh _ _ _ _ hMesh (hGood .p)
      hSafe.alphabet (hSafe.candidate choice.candidate) (fun q => (hSafe.lambdaOccurrences q).1) (fun q => (hSafe.lambdaOccurrences q).2))
    (GeneralPaperDeltaArrayPrice.signed_bit_work price hMono W m lambda Qv mesh _ _ _ _ hMesh (hGood .q)
      hSafe.alphabet (hSafe.response choice.response) (fun q => (hSafe.muOccurrences q).1) (fun q => (hSafe.muOccurrences q).2))
    (GeneralPaperDeltaArrayPrice.unsigned_bit_work price hMono W m lambda Qv mesh false _ _ _ hMesh (hGood .q) (hGood .lambda))
    (GeneralPaperDeltaArrayPrice.unsigned_bit_work price hMono W m lambda Qv mesh true _ _ _ hMesh (hGood .p) (hGood .mu))
    (GeneralPaperDeltaArrayPrice.signed_bit_work price hMono W m lambda Qv mesh _ _ _ _ hMesh (hGood .p)
      hSafe.alphabet (hSafe.candidate choice.candidate) (fun q => (hSafe.lambdaCells q).1) (fun q => (hSafe.lambdaCells q).2))
    (GeneralPaperDeltaArrayPrice.signed_bit_work price hMono W m lambda Qv mesh _ _ _ _ hMesh (hGood .q)
      hSafe.alphabet (hSafe.response choice.response) (fun q => (hSafe.muCells q).1) (fun q => (hSafe.muCells q).2))) _

theorem arithmetic_work {k : ℕ} (mesh : ℕ) (state : State k) (snapshot : Snapshot k) (choice : Choice state.plan) :
    (run false (fun _ => 1) (fun _ => 1) 1 mesh state snapshot choice).2≤arithmeticProfile state := by
  exact Nat.add_le_add_right (total_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (GeneralPaperDeltaArrayPrice.unsigned_arithmetic_work mesh false _ _ _)
    (GeneralPaperDeltaArrayPrice.unsigned_arithmetic_work mesh true _ _ _)
    (GeneralPaperDeltaArrayPrice.signed_arithmetic_work mesh _ _ _ _)
    (GeneralPaperDeltaArrayPrice.signed_arithmetic_work mesh _ _ _ _)
    (GeneralPaperDeltaArrayPrice.unsigned_arithmetic_work mesh false _ _ _)
    (GeneralPaperDeltaArrayPrice.unsigned_arithmetic_work mesh true _ _ _)
    (GeneralPaperDeltaArrayPrice.signed_arithmetic_work mesh _ _ _ _)
    (GeneralPaperDeltaArrayPrice.signed_arithmetic_work mesh _ _ _ _)) _

theorem profile_bound {k : ℕ} (price : ℕ → ℕ) (W m lambda Qv B : ℕ) (state : State k)
    (hS : (GeneralPaperSourceParameters.prepare k).summarySize≤B)
    (hp : state.plan.pCells.partition.count≤B) (hq : state.plan.qCells.partition.count≤B)
    (hl : state.plan.lambdaCells.partition.count≤B) (hm : state.plan.muCells.partition.count≤B) :
    profile price W m lambda Qv state≤uniformProfile price W m lambda k Qv B := by
  have h := Nat.add_le_add_right (total_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (GeneralPaperDeltaArrayPrice.unsigned_profile_mono price W m lambda k Qv _ B hS)
    (GeneralPaperDeltaArrayPrice.unsigned_profile_mono price W m lambda k Qv _ B hS)
    (GeneralPaperDeltaArrayPrice.signed_profile_mono price W m lambda k Qv _ B hS)
    (GeneralPaperDeltaArrayPrice.signed_profile_mono price W m lambda k Qv _ B hS)
    (GeneralPaperDeltaArrayPrice.unsigned_profile_mono price W m lambda k Qv _ B hp)
    (GeneralPaperDeltaArrayPrice.unsigned_profile_mono price W m lambda k Qv _ B hq)
    (GeneralPaperDeltaArrayPrice.signed_profile_mono price W m lambda k Qv _ B hl)
    (GeneralPaperDeltaArrayPrice.signed_profile_mono price W m lambda k Qv _ B hm)) (256*W)
  exact h.trans_eq (by unfold uniformProfile total; ring)

theorem linear_mono (n N K : ℕ) (hN : n≤N) : n*K+44*(n+1)≤N*K+44*(N+1) :=
  Nat.add_le_add (Nat.mul_le_mul_right K hN) (Nat.mul_le_mul_left 44 (by omega))

theorem arithmetic_profile_bound {k : ℕ} (B : ℕ) (state : State k)
    (hS : (GeneralPaperSourceParameters.prepare k).summarySize≤B)
    (hp : state.plan.pCells.partition.count≤B) (hq : state.plan.qCells.partition.count≤B)
    (hl : state.plan.lambdaCells.partition.count≤B) (hm : state.plan.muCells.partition.count≤B) :
    arithmeticProfile state≤uniformArithmeticProfile k B := by
  have h := Nat.add_le_add_right (total_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (linear_mono _ B (GeneralPaperUnsignedDeltaStepPrice.arithmeticProfile k+32) hS)
    (linear_mono _ B (GeneralPaperUnsignedDeltaStepPrice.arithmeticProfile k+32) hS)
    (linear_mono _ B (GeneralPaperSignedDeltaStepPrice.arithmeticProfile k+32) hS)
    (linear_mono _ B (GeneralPaperSignedDeltaStepPrice.arithmeticProfile k+32) hS)
    (linear_mono _ B (GeneralPaperUnsignedDeltaStepPrice.arithmeticProfile k+32) hp)
    (linear_mono _ B (GeneralPaperUnsignedDeltaStepPrice.arithmeticProfile k+32) hq)
    (linear_mono _ B (GeneralPaperSignedDeltaStepPrice.arithmeticProfile k+32) hl)
    (linear_mono _ B (GeneralPaperSignedDeltaStepPrice.arithmeticProfile k+32) hm)) 256
  exact h.trans_eq (by
    unfold uniformArithmeticProfile GeneralPaperDeltaArrayPrice.unsignedArithmeticProfile
      GeneralPaperDeltaArrayPrice.signedArithmeticProfile total
    ring)

end Blotto.GeneralPaperFieldDeltaPrice
