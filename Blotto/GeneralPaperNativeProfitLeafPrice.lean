import Blotto.GeneralPaperNativeProfitLeafExecution

/-! Complete native ordered-profit leaf prices. Reached tail counts and
retained source records derive all operand and annotation bounds. The field
coefficient is computed once outside the option fill in both models.
-/
namespace Blotto.GeneralPaperNativeProfitLeafPrice
open GeneralPaperNativeProfitLeafExecution
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperSummaryArrayExecution (arrayWord)
open GeneralPaperMeshQueryMetadata (referenceWord)
open GeneralPaperMeshPrefixInvariant (Good)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096
variable {R : Type}

def elementProfile (price : ℕ → ℕ) (W m lambda k Qv : ℕ) : ℕ :=
  GeneralPaperMeshPairPrice.tailsProfile price W m lambda k Qv+
    8*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+64*W+128*referenceWord W k

def profile (price : ℕ → ℕ) (W m lambda k Qv K : ℕ) : ℕ :=
  4*price (GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+64*W+
    (K*elementProfile price W m lambda k Qv+44*(K+1)*arrayWord W K)+64*W

def arithmeticElementProfile (k : ℕ) : ℕ := GeneralPaperMeshPairPrice.tailsArithmeticProfile k+200
def arithmeticProfile (K k : ℕ) : ℕ := 68+(K*arithmeticElementProfile k+44*(K+1))+64

theorem element_bit_work {K k : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda Qv T weight : ℕ)
    (prefixes : Prefix k) (plan : GeneralPaperOrderedNativeOptionProfits.Plan R k K) (i : Fin K)
    (hT : T=(GeneralPaperTrajectoryParameters.prepare lambda k).rows) (hWeight : weight≤Qv)
    (hMesh : plan.mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hGood : Good m lambda k Qv prefixes) :
    (element true price W (2*T*weight) prefixes plan i).2≤elementProfile price W m lambda k Qv := by
  let queried := GeneralPaperMeshPairExecution.tails true price W plan.mesh prefixes plan.tails i
  have hq := GeneralPaperMeshPairPrice.tails_bit_work price hMono W m lambda Qv plan.mesh prefixes plan.tails i hMesh hGood
  have hp := GeneralPaperMeshCountBounds.cached_interval_bound true price W m lambda Qv plan.mesh prefixes plan.tails.positive
    i.castSucc (Fin.last K) hMesh hGood
  have hn := GeneralPaperMeshCountBounds.cached_interval_bound true price W m lambda Qv plan.mesh prefixes plan.tails.negative
    i.castSucc (Fin.last K) hMesh hGood
  have hs := GeneralPaperNativeProfitScalarPrice.profit_work price hMono W m lambda k Qv T plan.mesh weight
    queried.1.positive queried.1.negative hT hMesh hWeight hp hn
  have hm := GeneralPaperMeshQueryMetadata.add_work price hMono m lambda k Qv queried.1.work 24 (by
    rw [GeneralPaperMeshPairExecution.tails_data true price W plan.mesh _ _ _ hMesh,GeneralPaperSignedTailPlan.evaluate_work]
    unfold GeneralPaperMeshQueryMetadata.cap; omega)
  have h := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hq hs) hm) (128*referenceWord W k)
  exact h.trans_eq (by unfold elementProfile; ring)

theorem element_arithmetic_work {K k : ℕ} (coefficient : ℕ) (prefixes : Prefix k)
    (plan : GeneralPaperOrderedNativeOptionProfits.Plan R k K) (i : Fin K) :
    (element false (fun _ => 1) 1 coefficient prefixes plan i).2≤arithmeticElementProfile k := by
  have hq := GeneralPaperMeshPairPrice.tails_arithmetic_work plan.mesh prefixes plan.tails i
  unfold element
  dsimp only
  rw [GeneralPaperNativeProfitScalarPrice.profit_arithmetic]
  change (GeneralPaperMeshPairExecution.tails false (fun _ => 1) 1 plan.mesh prefixes plan.tails i).2+70+2+128≤_
  unfold arithmeticElementProfile
  omega

theorem bit_work {K k : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W m lambda Qv T weight : ℕ)
    (prefixes : Prefix k) (plan : GeneralPaperOrderedNativeOptionProfits.Plan R k K)
    (hT : T=(GeneralPaperTrajectoryParameters.prepare lambda k).rows) (hWeight : weight≤Qv)
    (hMesh : plan.mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hGood : Good m lambda k Qv prefixes) :
    (run true (fun w => w) price W T weight prefixes plan).2≤profile price W m lambda k Qv K := by
  have hc := GeneralPaperNativeProfitScalarPrice.coefficient_work price hMono W m lambda k Qv T plan.mesh weight hT hMesh hWeight
  have ha := GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W K) _
    (element true price W (2*T*weight) prefixes plan)
    (GeneralPaperSummaryArrayControls.array_word_positive W K) (GeneralPaperSummaryArrayControls.array_index W K)
    (fun i => element_bit_work price hMono W m lambda Qv T weight prefixes plan i hT hWeight hMesh hGood)
  exact Nat.add_le_add_right (Nat.add_le_add hc ha) _

theorem arithmetic_work {K k : ℕ} (price : ℕ → ℕ) (T weight : ℕ) (prefixes : Prefix k)
    (plan : GeneralPaperOrderedNativeOptionProfits.Plan R k K) :
    (run false (fun _ => 1) price 1 T weight prefixes plan).2≤arithmeticProfile K k := by
  have hc := GeneralPaperNativeProfitScalarPrice.coefficient_arithmetic T weight
  have ha := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 _ (element false (fun _ => 1) 1 (2*T*weight) prefixes plan)
    (Nat.le_refl _) (fun _ _ => Nat.le_refl _) (fun i => element_arithmetic_work _ prefixes plan i)
  change (GeneralPaperNativeProfitScalarPrice.coefficient (fun _ => 1) 1 T weight).2+
    (PaperIndexedArrayConstruction.run (fun _ => 1) 1 (element false (fun _ => 1) 1 (2*T*weight) prefixes plan)).2+64≤_
  rw [hc]
  unfold arithmeticProfile
  exact Nat.add_le_add_right (Nat.add_le_add_left (by simpa only [Nat.mul_one] using ha) 68) _

end Blotto.GeneralPaperNativeProfitLeafPrice
