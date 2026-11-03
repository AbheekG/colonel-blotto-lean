import Blotto.GeneralPaperDeltaArrayExecution

/-! Complete indexed occurrence/cell loops, including scalar callbacks,
array writes, control/index words and returned element projections. The
signed loops retain explicit full-code comparison prices.
-/
namespace Blotto.GeneralPaperDeltaArrayPrice
open GeneralPaperDeltaArrayExecution
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperSummaryArrayExecution (arrayWord)
open GeneralPaperMeshPrefixInvariant (Good)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def unsignedProfile (price : ℕ → ℕ) (W m lambda k Qv n : ℕ) : ℕ :=
  n*(GeneralPaperUnsignedDeltaStepPrice.profile price W m lambda k Qv+32*W)+44*(n+1)*arrayWord W n

def signedProfile (price : ℕ → ℕ) (W m lambda k Qv n : ℕ) : ℕ :=
  n*(GeneralPaperSignedDeltaStepPrice.profile price W m lambda k Qv+32*W)+44*(n+1)*arrayWord W n

def unsignedArithmeticProfile (n k : ℕ) : ℕ := n*(GeneralPaperUnsignedDeltaStepPrice.arithmeticProfile k+32)+44*(n+1)
def signedArithmeticProfile (n k : ℕ) : ℕ := n*(GeneralPaperSignedDeltaStepPrice.arithmeticProfile k+32)+44*(n+1)

theorem unsigned_bit_work {n k : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda Qv mesh : ℕ) (response : Bool)
    (cdfPrefix tailPrefix : Prefix k) (plan : GeneralPaperQueryLossCounts.Plan k n)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hCDF : Good m lambda k Qv cdfPrefix) (hTail : Good m lambda k Qv tailPrefix) :
    (unsigned true (fun w => w) price W mesh response cdfPrefix tailPrefix plan).2≤unsignedProfile price W m lambda k Qv n :=
  GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W n) _
    (unsignedElement true price W mesh response cdfPrefix tailPrefix plan)
    (GeneralPaperSummaryArrayControls.array_word_positive W n) (GeneralPaperSummaryArrayControls.array_index W n)
    (fun q => Nat.add_le_add_right (GeneralPaperUnsignedDeltaStepPrice.bit_work price hMono W m lambda Qv mesh response _ _ plan q hMesh hCDF hTail) _)

theorem signed_bit_work {n k : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda Qv mesh U bid : ℕ)
    (prefixes : Prefix k) (plan : GeneralPaperSignedUpdatePlan.Plan k n)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hGood : Good m lambda k Qv prefixes)
    (hU : U≤2^(lambda+1)) (hBid : bid≤2^(lambda+1))
    (hCode : ∀ q,plan.codes.read q≤2^(lambda+1)) (hPosition : ∀ q,plan.positions.read q≤2^(lambda+1)) :
    (signed true (fun w => w) price W mesh U bid prefixes plan).2≤signedProfile price W m lambda k Qv n :=
  GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W n) _ (signedElement true price W mesh U bid prefixes plan)
    (GeneralPaperSummaryArrayControls.array_word_positive W n) (GeneralPaperSummaryArrayControls.array_index W n)
    (fun q => Nat.add_le_add_right (GeneralPaperSignedDeltaStepPrice.bit_work price hMono W m lambda Qv mesh U bid prefixes plan q
      hMesh hGood hU hBid (hCode q) (hPosition q)) _)

theorem unsigned_arithmetic_work {n k : ℕ} (mesh : ℕ) (response : Bool) (cdfPrefix tailPrefix : Prefix k)
    (plan : GeneralPaperQueryLossCounts.Plan k n) :
    (unsigned false (fun _ => 1) (fun _ => 1) 1 mesh response cdfPrefix tailPrefix plan).2≤unsignedArithmeticProfile n k := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 _
    (unsignedElement false (fun _ => 1) 1 mesh response cdfPrefix tailPrefix plan) (Nat.le_refl _) (fun _ _ => Nat.le_refl _)
    (fun q => Nat.add_le_add_right (GeneralPaperUnsignedDeltaStepPrice.arithmetic_work mesh response cdfPrefix tailPrefix plan q) _)
  simpa only [unsigned,Bool.false_eq_true,ite_false,Nat.mul_one,unsignedArithmeticProfile] using h

theorem signed_arithmetic_work {n k : ℕ} (mesh U bid : ℕ) (prefixes : Prefix k) (plan : GeneralPaperSignedUpdatePlan.Plan k n) :
    (signed false (fun _ => 1) (fun _ => 1) 1 mesh U bid prefixes plan).2≤signedArithmeticProfile n k := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 _ (signedElement false (fun _ => 1) 1 mesh U bid prefixes plan)
    (Nat.le_refl _) (fun _ _ => Nat.le_refl _)
    (fun q => Nat.add_le_add_right (GeneralPaperSignedDeltaStepPrice.arithmetic_work mesh U bid prefixes plan q) _)
  simpa only [signed,Bool.false_eq_true,ite_false,Nat.mul_one,signedArithmeticProfile] using h

theorem unsigned_profile_mono (price : ℕ → ℕ) (W m lambda k Qv n N : ℕ) (hN : n≤N) :
    unsignedProfile price W m lambda k Qv n≤unsignedProfile price W m lambda k Qv N := by
  have hA := GeneralPaperPlanProfileMonotonicity.array_word W n N hN
  exact Nat.add_le_add (Nat.mul_le_mul_right _ hN)
    (Nat.mul_le_mul (Nat.mul_le_mul_left 44 (by omega : n+1≤N+1)) hA)

theorem signed_profile_mono (price : ℕ → ℕ) (W m lambda k Qv n N : ℕ) (hN : n≤N) :
    signedProfile price W m lambda k Qv n≤signedProfile price W m lambda k Qv N := by
  have hA := GeneralPaperPlanProfileMonotonicity.array_word W n N hN
  exact Nat.add_le_add (Nat.mul_le_mul_right _ hN)
    (Nat.mul_le_mul (Nat.mul_le_mul_left 44 (by omega : n+1≤N+1)) hA)

end Blotto.GeneralPaperDeltaArrayPrice
