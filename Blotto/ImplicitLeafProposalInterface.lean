import Blotto.ImplicitResourceSampler
import Blotto.NormalizedKernelMean

/-! Actual implicit resource draws realize the recursive proposal's total leaf
kernel. Empty prefixes return none; positivity and monotonicity derive a feasible
first code in every nonempty prefix. No numerical-label categorical list is
constructed by the native callback. -/

namespace Blotto
open scoped BigOperators Classical
namespace ImplicitLeafCounts

structure ProposalLeaf where
  cap : ℕ
  blocks : List Block
  partition : Partition cap blocks
  positive : Positive blocks
  decode : ℕ → ℚ
  monotone : MonotoneResourceCuts.MonotoneDecode cap decode

namespace ProposalLeaf

def family (leaf : ProposalLeaf) : RationalWeightedFamily (leaf.cap + 1) :=
  decodedFamily leaf.cap leaf.blocks (fun block hb => (leaf.positive block hb).le) leaf.decode

def bitBudget (leaf : ProposalLeaf) (K attempts : ℕ) : ℕ := prefixSampleBitBudget leaf.cap leaf.blocks.length K attempts

def sample (leaf : ProposalLeaf) (budget : ℚ) (K attempts : ℕ)
    (bits : Fin (leaf.bitBudget K attempts) → Bool) : Option (Fin (leaf.cap + 1)) :=
  if hFirst : leaf.decode 0 ≤ budget then
    some (resourceSample leaf.cap leaf.blocks leaf.partition leaf.positive leaf.decode leaf.monotone budget hFirst K attempts bits)
  else none

noncomputable def actualKernel (leaf : ProposalLeaf) (budget : ℚ) (K attempts : ℕ) :
    BoundedExpectationKernel (Option (Fin (leaf.cap + 1))) := (fairBitKernel (leaf.bitBudget K attempts)).map (leaf.sample budget K attempts)

noncomputable def idealKernel (leaf : ProposalLeaf) (budget : ℚ) :
    BoundedExpectationKernel (Option (Fin (leaf.cap + 1))) :=
  totalNormalizedKernel (RationalWeightedGuideTree.leafWeights leaf.family budget)
    (RationalWeightedGuideTree.leafWeights_nonnegative leaf.family budget)

theorem prefix_positive_iff (leaf : ProposalLeaf) (budget : ℚ) :
    0 < leaf.family.prefixMass budget ↔ leaf.decode 0 ≤ budget := by
  constructor
  · intro hp
    by_contra hn
    have hz : leaf.family.prefixMass budget = 0 := by
      unfold RationalWeightedFamily.prefixMass family decodedFamily
      apply Finset.sum_eq_zero
      intro code _
      have hm := leaf.monotone 0 code.val (Nat.zero_le _) (by omega)
      rw [ite_eq_right (by linarith : ¬leaf.decode code.val ≤ budget)]
    rw [hz] at hp
    exact lt_irrefl _ hp
  · intro hFirst
    have he := decodedFamily_prefixMass leaf.cap leaf.blocks leaf.partition
      (fun block hb => (leaf.positive block hb).le) leaf.decode leaf.monotone budget
    change leaf.family.prefixMass budget = _ at he
    rw [he]
    exact partition_prefixMass_positive leaf.cap leaf.blocks leaf.partition leaf.positive _
      (resourceCap_nonnegative leaf.cap leaf.decode leaf.monotone budget hFirst)

theorem sample_some_contract (leaf : ProposalLeaf) (budget : ℚ) (K attempts : ℕ)
    (bits : Fin (leaf.bitBudget K attempts) → Bool) (label : Fin (leaf.cap + 1))
    (h : leaf.sample budget K attempts bits = some label) :
    leaf.family.resource label ≤ budget ∧ 0 < leaf.family.mass label := by
  unfold sample at h
  split at h
  · rename_i hFirst
    have he := Option.some.inj h
    rw [← he]
    exact ⟨resourceSample_feasible leaf.cap leaf.blocks leaf.partition leaf.positive leaf.decode leaf.monotone budget hFirst K attempts bits,
      partition_labelMass_positive leaf.cap leaf.blocks leaf.partition leaf.positive _⟩
  · cases h

theorem sample_none_iff (leaf : ProposalLeaf) (budget : ℚ) (K attempts : ℕ)
    (bits : Fin (leaf.bitBudget K attempts) → Bool) :
    leaf.sample budget K attempts bits = none ↔ leaf.family.prefixMass budget = 0 := by
  have hn := leaf.family.prefixMass_nonnegative budget
  by_cases hFirst : leaf.decode 0 ≤ budget
  · have hp := (leaf.prefix_positive_iff budget).mpr hFirst
    simp only [sample, hFirst, dite_true, Option.some_ne_none, false_iff]
    exact ne_of_gt hp
  · have hNo : ¬0 < leaf.family.prefixMass budget := fun hp => hFirst ((leaf.prefix_positive_iff budget).mp hp)
    have hz : leaf.family.prefixMass budget = 0 := le_antisymm (le_of_not_gt hNo) hn
    simp only [sample, hFirst, dite_false, hz]

theorem idealKernel_positive_mean (leaf : ProposalLeaf) (budget : ℚ) (hFirst : leaf.decode 0 ≤ budget)
    (test : Option (Fin (leaf.cap + 1)) → ℝ) :
    (leaf.idealKernel budget).mean test =
      (∑ code : Fin (leaf.cap + 1), if leaf.decode code.val ≤ budget
        then (labelMass leaf.blocks code.val : ℝ) * test (some code) else 0) / (leaf.family.prefixMass budget : ℝ) := by
  have hp := (leaf.prefix_positive_iff budget).mpr hFirst
  have hSum : 0 < ∑ code, RationalWeightedGuideTree.leafWeights leaf.family budget code := hp
  unfold idealKernel
  rw [totalNormalizedKernel_mean _ _ hSum]
  have hTotal : (∑ code, RationalWeightedGuideTree.leafWeights leaf.family budget code) = leaf.family.prefixMass budget := rfl
  rw [hTotal]
  simp only [div_eq_mul_inv, Rat.cast_mul, Rat.cast_inv]
  simp_rw [mul_right_comm _ _ (test (some _))]
  rw [← Finset.sum_mul]
  apply congrArg (fun numerator => numerator * (leaf.family.prefixMass budget : ℝ)⁻¹)
  apply Finset.sum_congr rfl
  intro code _
  unfold RationalWeightedGuideTree.leafWeights family decodedFamily
  split_ifs <;> simp

theorem actualKernel_close (leaf : ProposalLeaf) (budget : ℚ) (K attempts : ℕ) :
    (leaf.actualKernel budget K attempts).Close (leaf.idealKernel budget)
      (1 / (2 : ℝ) ^ K + 1 / (2 : ℝ) ^ attempts) := by
  intro test hTest
  by_cases hFirst : leaf.decode 0 ≤ budget
  · have he := resourceSample_mean_error leaf.cap leaf.blocks leaf.partition leaf.positive leaf.decode leaf.monotone
      budget hFirst K attempts (fun code => test (some code)) (fun code => hTest _)
    change |(fairBitKernel (leaf.bitBudget K attempts)).mean (fun bits => test (some
      (resourceSample leaf.cap leaf.blocks leaf.partition leaf.positive leaf.decode leaf.monotone budget hFirst K attempts bits))) -
        (∑ code : Fin (leaf.cap + 1), if leaf.decode code.val ≤ budget then (labelMass leaf.blocks code.val : ℝ) * test (some code) else 0) /
          (leaf.family.prefixMass budget : ℝ)| ≤ _ at he
    rw [← leaf.idealKernel_positive_mean budget hFirst test] at he
    change |(fairBitKernel (leaf.bitBudget K attempts)).mean (fun bits => test (leaf.sample budget K attempts bits)) - _| ≤ _
    simp only [sample, hFirst, dite_true]
    exact he
  · have hp : ¬0 < leaf.family.prefixMass budget := fun hp => hFirst ((leaf.prefix_positive_iff budget).mp hp)
    have hi := totalNormalizedKernel_zero_mean (RationalWeightedGuideTree.leafWeights leaf.family budget)
      (RationalWeightedGuideTree.leafWeights_nonnegative leaf.family budget) hp test
    change (leaf.idealKernel budget).mean test = test none at hi
    change |(fairBitKernel (leaf.bitBudget K attempts)).mean (fun bits => test (leaf.sample budget K attempts bits)) - _| ≤ _
    simp only [sample, hFirst, dite_false]
    rw [(fairBitKernel _).constant, hi]
    simp only [sub_self, abs_zero]
    positivity

end ProposalLeaf
end ImplicitLeafCounts
end Blotto
