import Blotto.RationalProposalNodeSampler

/-! Native recursive proposal follows one local choice and one visit to each
child at the exact residual budgets. Node seeds occupy distinct tree addresses;
full independent-block law/error and arithmetic-price composition remain open. -/

namespace Blotto
open scoped BigOperators
namespace RationalWeightedGuideTree

def sampleRecord : (tree : RationalWeightedGuideTree) → ℚ → ℕ → (ℕ → ℕ → Bool) → Option tree.Record
  | .leaf family _ _, B, K, seeds => family.conditionalSample B K (seeds 0)
  | .fork _ _ left right, B, K, seeds =>
      match left.guide.syntheticSample right.guide B K (seeds 0) with
      | none => none
      | some i =>
        match right.sampleRecord (B - left.guide.resource i) K (fun node => seeds (1 + node)) with
        | none => none
        | some r =>
          match left.sampleRecord (B - right.resource r) K (fun node => seeds (1 + right.nodes + node)) with
          | none => none
          | some l => some (i, r, l)

theorem sampleRecord_positive (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (K : ℕ) (seeds : ℕ → ℕ → Bool) (record : tree.Record)
    (h : tree.sampleRecord B K seeds = some record) : 0 < tree.probability B record := by
  induction tree generalizing B seeds with
  | @leaf n p family guide gamma =>
    have hs := family.conditionalSample_contract B K (seeds 0) record h
    have hm : 0 < family.prefixMass B := by
      have hn : ∀ j ∈ (Finset.univ : Finset (Fin _)),
          0 ≤ if family.resource j ≤ B then family.mass j else 0 := by
        intro j _
        split_ifs
        · exact family.mass_nonnegative j
        · exact le_rfl
      have he := Finset.single_le_sum hn (@Finset.mem_univ (Fin n) (Fin.fintype n) record)
      exact hs.2.trans_le (by simpa only [RationalWeightedFamily.prefixMass, hs.1, ite_true] using he)
    change 0 < if family.resource record ≤ B then family.mass record / family.prefixMass B else 0
    rw [ite_eq_left hs.1]
    exact div_pos hs.2 hm
  | fork guide gamma left right ihL ihR =>
    unfold sampleRecord at h
    cases hi : left.guide.syntheticSample right.guide B K (seeds 0) with
    | none => rw [hi] at h; cases h
    | some i =>
      rw [hi] at h
      dsimp only at h
      cases hr : right.sampleRecord (B - left.guide.resource i) K (fun node => seeds (1 + node)) with
      | none => rw [hr] at h; cases h
      | some r =>
        rw [hr] at h
        dsimp only at h
        cases hl : left.sampleRecord (B - right.resource r) K (fun node => seeds (1 + right.nodes + node)) with
        | none => rw [hl] at h; cases h
        | some l =>
          rw [hl] at h
          dsimp only at h
          cases Option.some.inj h
          have hqR := ihR hc.2.2.1 _ _ r hr
          have hqL := ihL hc.2.1 _ _ l hl
          have hselected := left.guide.syntheticSample_positive right.guide B K (seeds 0) i hi
          have hz := left.guide.selected_convolution_positive right.guide B i hselected
          change 0 < (left.guide.mass i * right.guidePrefix (B - left.guide.resource i) /
            left.guide.convolution right.guide B) * right.probability (B - left.guide.resource i) r *
              left.probability (B - right.resource r) l
          exact mul_pos (mul_pos (div_pos hselected hz) hqR) hqL

theorem sampleRecord_feasible (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (K : ℕ) (seeds : ℕ → ℕ → Bool) (record : tree.Record)
    (h : tree.sampleRecord B K seeds = some record) : tree.resource record ≤ B :=
  tree.positive_feasible hc B record (tree.sampleRecord_positive hc B K seeds record h)

theorem node_addresses_disjoint (_left right : RationalWeightedGuideTree)
    (r : ℕ) (hr : r < right.nodes) (l : ℕ) : 1 + r ≠ 1 + right.nodes + l := by omega

def nodeBitBudget : RationalWeightedGuideTree → ℕ → ℕ
  | .leaf (n := n) _ _ _, K => 3 * (n - 1 + K)
  | .fork _ _ left _, K => 3 * (left.guideSize - 1 + K)

def totalBitBudget : RationalWeightedGuideTree → ℕ → ℕ
  | .leaf (n := n) _ _ _, K => 3 * (n - 1 + K)
  | .fork _ _ left right, K => 3 * (left.guideSize - 1 + K) + right.totalBitBudget K + left.totalBitBudget K

end RationalWeightedGuideTree
end Blotto
