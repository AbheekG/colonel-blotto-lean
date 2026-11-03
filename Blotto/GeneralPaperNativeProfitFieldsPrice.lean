import Blotto.GeneralPaperNativeProfitFieldsExecution

/-! Complete weighted native DP-input list prices. The retained horizon,
per-field cached mesh, actual prefix invariants and rounded-value sum derive
all leaf premises. List control words come from the retained field count.
-/
namespace Blotto.GeneralPaperNativeProfitFieldsPrice
open scoped BigOperators
open GeneralPaperNativeProfitFieldsExecution
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperSummaryArrayExecution (arrayWord)
open GeneralPaperMeshPrefixInvariant (Good)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096
variable {R : Type}

def profile (price : ℕ → ℕ) (W m lambda k Qv K : ℕ) : ℕ :=
  m*(GeneralPaperNativeProfitLeafPrice.profile price W m lambda k Qv K+64*W+72*arrayWord W (m+2))+18*arrayWord W (m+2)

def arithmeticProfile (m K k : ℕ) : ℕ := m*(GeneralPaperNativeProfitLeafPrice.arithmeticProfile K k+136)+18

theorem weight_bound {m : ℕ} (weights : FixedArrayTable m ℕ) (Qv : ℕ) (hWeights : ∑ j,weights.read j=Qv) (j : Fin m) :
    weights.read j≤Qv := by
  rw [←hWeights]
  exact Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ j)

theorem bit_work {m K k : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W lambda Qv T : ℕ) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (Prefix k)) (plans : FixedArrayTable m (GeneralPaperOrderedNativeOptionProfits.Plan R k K))
    (hT : T=(GeneralPaperTrajectoryParameters.prepare lambda k).rows) (hWeights : ∑ j,weights.read j=Qv)
    (hMesh : ∀ j,(plans.read j).mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hGood : ∀ j,Good m lambda k Qv (prefixes.read j)) :
    (run true (fun w => w) price W T weights prefixes plans).2≤profile price W m lambda k Qv K := by
  have hIndex (r : ℕ) (hr : r<m) : binaryWordWidth (r+1)+1≤arrayWord W (m+2) := by
    have h := binaryWordWidth_mono (show r+1≤m+2+1 by omega)
    unfold arrayWord; omega
  have he (j : Fin m) : (element true (fun w => w) price W T weights prefixes plans j).2≤
      GeneralPaperNativeProfitLeafPrice.profile price W m lambda k Qv K+64*W :=
    Nat.add_le_add_right (GeneralPaperNativeProfitLeafPrice.bit_work price hMono W m lambda Qv T (weights.read j)
      (prefixes.read j) (plans.read j) hT (weight_bound weights Qv hWeights j) (hMesh j) (hGood j)) _
  exact GeneralPaperIndexedListPrice.work (fun w => w) (arrayWord W (m+2)) _ _
    (GeneralPaperSummaryArrayControls.array_word_positive W (m+2)) hIndex he

theorem arithmetic_work {m K k : ℕ} (price : ℕ → ℕ) (T : ℕ) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (Prefix k)) (plans : FixedArrayTable m (GeneralPaperOrderedNativeOptionProfits.Plan R k K)) :
    (run false (fun _ => 1) price 1 T weights prefixes plans).2≤arithmeticProfile m K k := by
  have he (j : Fin m) : (element false (fun _ => 1) price 1 T weights prefixes plans j).2≤
      GeneralPaperNativeProfitLeafPrice.arithmeticProfile K k+64 :=
    Nat.add_le_add_right (GeneralPaperNativeProfitLeafPrice.arithmetic_work price T (weights.read j) (prefixes.read j) (plans.read j)) _
  have h := GeneralPaperIndexedListPrice.work (fun _ => 1) 1 _ _ (Nat.le_refl _) (fun _ _ => Nat.le_refl _) he
  simpa only [run,Bool.false_eq_true,ite_false,Nat.mul_one,arithmeticProfile,Nat.add_assoc] using h

end Blotto.GeneralPaperNativeProfitFieldsPrice
