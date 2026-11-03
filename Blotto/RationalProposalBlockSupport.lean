import Blotto.RationalProposalNativeError

/-! The direct finite-block implementation returns only positive-Q feasible
records on every bit input. Distributional accuracy is separate from this
pointwise support guarantee, including zero-weight categorical branches. -/

namespace Blotto
open scoped BigOperators
namespace RationalWeightedGuideTree

theorem sampleBlocks_positive (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (K : ℕ) (bits : Fin (tree.totalBitBudget K) → Bool) (record : tree.Record)
    (h : tree.sampleBlocks B K bits = some record) : 0 < tree.probability B record := by
  induction tree generalizing B with
  | leaf family guide gamma =>
    have hs := family.conditionalSample_contract B K (finiteBitReader bits) record h
    have hMean : 0 < family.prefixMass B := by
      have hn : ∀ j ∈ (Finset.univ : Finset (Fin _)),
          0 ≤ if family.resource j ≤ B then family.mass j else 0 := by
        intro j _
        split_ifs
        · exact family.mass_nonnegative j
        · exact le_rfl
      have he := Finset.single_le_sum hn (@Finset.mem_univ (Fin _) (Fin.fintype _) record)
      exact hs.2.trans_le (by simpa only [RationalWeightedFamily.prefixMass, hs.1, ite_true] using he)
    change 0 < if family.resource record ≤ B then family.mass record / family.prefixMass B else 0
    rw [ite_eq_left hs.1]
    exact div_pos hs.2 hMean
  | fork guide gamma left right ihL ihR =>
    unfold sampleBlocks at h
    dsimp only at h
    split at h
    · cases h
    · rename_i i hi
      split at h
      · cases h
      · rename_i r hr
        cases hl : left.sampleBlocks (B - right.resource r) K _ with
        | none => rw [hl] at h; cases h
        | some l =>
          rw [hl] at h
          cases Option.some.inj h
          have hqR := ihR hc.2.2.1 _ _ r hr
          have hqL := ihL hc.2.1 _ _ l hl
          have hselected := left.guide.syntheticSample_positive right.guide B K _ i hi
          have hz := left.guide.selected_convolution_positive right.guide B i hselected
          change 0 < (left.guide.mass i * right.guidePrefix (B - left.guide.resource i) /
            left.guide.convolution right.guide B) * right.probability (B - left.guide.resource i) r *
              left.probability (B - right.resource r) l
          exact mul_pos (mul_pos (div_pos hselected hz) hqR) hqL

theorem sampleBlocks_feasible (tree : RationalWeightedGuideTree) (hc : tree.real.LowerCertified)
    (B : ℚ) (K : ℕ) (bits : Fin (tree.totalBitBudget K) → Bool) (record : tree.Record)
    (h : tree.sampleBlocks B K bits = some record) : tree.resource record ≤ B :=
  tree.positive_feasible hc B record (tree.sampleBlocks_positive hc B K bits record h)

end RationalWeightedGuideTree
end Blotto
