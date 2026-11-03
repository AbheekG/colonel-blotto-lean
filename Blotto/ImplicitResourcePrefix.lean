import Blotto.ImplicitLeafIntervalMass
import Blotto.MonotonePlateauBounds

/-! Exact resource-prefix access reduces to the computed signed code cutoff.
Duplicate decoded labels and negative cutoffs remain in the original finite
family; executable evaluation calls the decoder only through binary search. -/

namespace Blotto.ImplicitLeafCounts
open scoped BigOperators Classical

def decodedFamily (C : ℕ) (blocks : List Block) (hn : Nonnegative blocks)
    (decode : ℕ → ℚ) : RationalWeightedFamily (C + 1) where
  resource := fun code => decode code.val
  mass := fun code => labelMass blocks code.val
  mass_nonnegative := fun code => labelMass_nonnegative blocks code.val hn

theorem decodedFamily_prefixMass (C : ℕ) (blocks : List Block) (hp : Partition C blocks)
    (hn : Nonnegative blocks) (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode)
    (budget : ℚ) :
    (decodedFamily C blocks hn decode).prefixMass budget =
      prefixMass blocks (MonotoneResourceCuts.cap C decode budget) := by
  rw [partition_prefixMass_labels C blocks hp]
  unfold RationalWeightedFamily.prefixMass decodedFamily
  apply Finset.sum_congr rfl
  intro code _
  change (if decode code.val ≤ budget then labelMass blocks code.val else 0) = _
  simp only [MonotoneResourceCuts.cap_contract C decode hm budget code.val (by omega)]

theorem decodedFamily_prefix_at_plateau (C : ℕ) (blocks : List Block) (hp : Partition C blocks)
    (hn : Nonnegative blocks) (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode)
    (code : Fin (C + 1)) :
    (decodedFamily C blocks hn decode).prefixMass (decode code.val) =
      prefixMass blocks (MonotoneResourceCuts.plateauEnd C decode code.val : ℤ) := by
  rw [decodedFamily_prefixMass C blocks hp hn decode hm]
  have he : MonotoneResourceCuts.cap C decode (decode code.val) =
      (MonotoneResourceCuts.plateauEnd C decode code.val : ℤ) := by
    have hp := MonotoneResourceCuts.code_lt_strict_self C decode hm code.val (by omega)
    unfold MonotoneResourceCuts.cap MonotoneResourceCuts.plateauEnd
    omega
  rw [he]

def resourcePrefixWithVisits (C : ℕ) (blocks : List Block) (decode : ℕ → ℚ) (budget : ℚ) : ℚ × ℕ :=
  let cutoff := MonotoneResourceCuts.strict C decode budget
  let queried := prefixMassWithVisits blocks ((cutoff.1 : ℤ) - 1)
  (queried.1, cutoff.2 + queried.2)

theorem resourcePrefixWithVisits_state (C : ℕ) (blocks : List Block) (hp : Partition C blocks)
    (hn : Nonnegative blocks) (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode)
    (budget : ℚ) :
    (resourcePrefixWithVisits C blocks decode budget).1 = (decodedFamily C blocks hn decode).prefixMass budget := by
  unfold resourcePrefixWithVisits
  dsimp only
  rw [prefixMassWithVisits_refines]
  exact (decodedFamily_prefixMass C blocks hp hn decode hm budget).symm

theorem resourcePrefixWithVisits_bound (C : ℕ) (blocks : List Block) (decode : ℕ → ℚ) (budget : ℚ) :
    (resourcePrefixWithVisits C blocks decode budget).2 ≤ binaryWordWidth (C + 1) + blocks.length := by
  have hs := MonotoneCodeSearch.first_visits C (MonotoneResourceCuts.strictPredicate decode budget)
  change (MonotoneResourceCuts.strict C decode budget).2 ≤ _ at hs
  unfold resourcePrefixWithVisits
  dsimp only
  rw [prefixMassWithVisits_refines]
  dsimp only
  omega

theorem resourcePrefixWithVisits_negative (C : ℕ) (blocks : List Block) (hp : Partition C blocks)
    (hn : Nonnegative blocks) (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode)
    (hNonnegative : ∀ code ≤ C, 0 ≤ decode code) (budget : ℚ) (hb : budget < 0) :
    (resourcePrefixWithVisits C blocks decode budget).1 = 0 := by
  rw [resourcePrefixWithVisits_state C blocks hp hn decode hm budget]
  unfold RationalWeightedFamily.prefixMass decodedFamily
  apply Finset.sum_eq_zero
  intro code _
  have hc := hNonnegative code.val (by omega)
  rw [ite_eq_right (by linarith : ¬decode code.val ≤ budget)]

noncomputable def realCap (C : ℕ) (decode : ℕ → ℚ) (threshold : ℝ) : ℤ :=
  (MonotoneCodeSearch.first C (fun code => decide (threshold < (decode code : ℝ)))).1 - (1 : ℤ)

theorem realCap_contract (C : ℕ) (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode)
    (threshold : ℝ) (code : ℕ) (hc : code ≤ C) :
    (decode code : ℝ) ≤ threshold ↔ (code : ℤ) ≤ realCap C decode threshold := by
  have hMono : MonotoneCodeSearch.IsMonotone C (fun k => decide (threshold < (decode k : ℝ))) := by
    intro i j hij hj hp
    apply decide_eq_true
    have hi : threshold < (decode i : ℝ) := of_decide_eq_true hp
    have he : (decode i : ℝ) ≤ decode j := by exact_mod_cast hm i j hij hj
    exact hi.trans_le he
  have hs := (MonotoneCodeSearch.first_contract C (fun k => decide (threshold < (decode k : ℝ))) hMono).2 code hc
  simp only [decide_eq_true_eq] at hs
  have he : (decode code : ℝ) ≤ threshold ↔ code <
      (MonotoneCodeSearch.first C (fun k => decide (threshold < (decode k : ℝ)))).1 := by
    rw [← not_lt, hs, not_le]
  rw [he]
  unfold realCap
  omega

theorem decodedFamily_real_prefix (C : ℕ) (blocks : List Block) (hp : Partition C blocks)
    (hn : Nonnegative blocks) (decode : ℕ → ℚ) (hm : MonotoneResourceCuts.MonotoneDecode C decode)
    (threshold : ℝ) :
    (decodedFamily C blocks hn decode).real.prefixMass threshold =
      (prefixMass blocks (realCap C decode threshold) : ℝ) := by
  rw [partition_prefixMass_labels C blocks hp]
  unfold RationalWeightedFamily.real WeightedResourceFamily.prefixMass decodedFamily
  push_cast
  apply Finset.sum_congr rfl
  intro code _
  simp only [realCap_contract C decode hm threshold code.val (by omega)]
  split_ifs <;> simp

end Blotto.ImplicitLeafCounts
