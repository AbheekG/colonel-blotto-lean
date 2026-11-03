import Blotto.ImplicitLeafUpperGuideSize
import Blotto.CumulativeInternalGuide
import Blotto.ImplicitLeafProposalInterface

/-! The actual implicit upper leaf guide becomes a certified lower guide by
dividing every positive bin mass by gamma. Resources, original labelled leaves
and logarithmic bin count are preserved. No upper guide is silently inserted
into the lower-oriented sampler. -/

namespace Blotto
open scoped BigOperators Classical
namespace ImplicitLeafCounts
namespace ProposalLeaf

def lowerGuideAtoms (leaf : ProposalLeaf) (gamma : ℚ) : List CumulativeGuidePruning.Atom :=
  (upperGuide leaf.cap leaf.blocks leaf.decode gamma).map (fun atom => (atom.1, atom.2 / gamma))

theorem lowerGuideAtoms_nonnegative (leaf : ProposalLeaf) (gamma : ℚ) (hg : 1 ≤ gamma) :
    CumulativeGuidePruning.Nonnegative (leaf.lowerGuideAtoms gamma) := by
  intro atom ha
  rcases List.mem_map.mp ha with ⟨source, hs, rfl⟩
  rcases List.mem_map.mp hs with ⟨bin, hb, rfl⟩
  exact div_nonneg (upperGuide_positive leaf.cap leaf.blocks leaf.partition leaf.positive leaf.decode leaf.monotone gamma hg 0 (by omega) bin hb).le (by linarith)

def lowerGuide (leaf : ProposalLeaf) (gamma : ℚ) (hg : 1 ≤ gamma) :
    RationalWeightedFamily (leaf.lowerGuideAtoms gamma).length :=
  CumulativeGuidePruning.rationalFamily (leaf.lowerGuideAtoms gamma) (leaf.lowerGuideAtoms_nonnegative gamma hg)

theorem lowerGuideAtoms_length (leaf : ProposalLeaf) (gamma : ℚ) :
    (leaf.lowerGuideAtoms gamma).length = (upperGuide leaf.cap leaf.blocks leaf.decode gamma).length := List.length_map _

theorem lowerGuideAtoms_prefix (leaf : ProposalLeaf) (gamma : ℚ) (threshold : ℝ) :
    CumulativeGuidePruning.prefixMass (leaf.lowerGuideAtoms gamma) threshold =
      CumulativeGuidePruning.prefixMass (upperGuide leaf.cap leaf.blocks leaf.decode gamma) threshold / gamma := by
  unfold lowerGuideAtoms
  generalize upperGuide leaf.cap leaf.blocks leaf.decode gamma = atoms
  induction atoms with
  | nil => simp [CumulativeGuidePruning.prefixMass]
  | cons atom rest ih =>
    simp only [List.map_cons, CumulativeGuidePruning.prefixMass]
    rw [ih]
    split_ifs <;> ring

theorem lowerGuide_certificate (leaf : ProposalLeaf) (gamma : ℚ) (hg : 1 ≤ gamma) (threshold : ℝ) :
    (leaf.lowerGuide gamma hg).real.prefixMass threshold ≤ leaf.family.real.prefixMass threshold ∧
      leaf.family.real.prefixMass threshold ≤ (gamma : ℝ) * (leaf.lowerGuide gamma hg).real.prefixMass threshold := by
  have hu := upperGuide_envelope leaf.cap leaf.blocks leaf.partition leaf.positive leaf.decode leaf.monotone gamma hg threshold
  have hTrue : leaf.family.real.prefixMass threshold =
      ((∑ code : Fin (leaf.cap + 1), if (leaf.decode code.val : ℝ) ≤ threshold then labelMass leaf.blocks code.val else 0 : ℚ) : ℝ) := by
    unfold ProposalLeaf.family decodedFamily RationalWeightedFamily.real WeightedResourceFamily.prefixMass
    push_cast
    apply Finset.sum_congr rfl
    intro code _
    split_ifs <;> simp
  have hGuide : (leaf.lowerGuide gamma hg).real.prefixMass threshold =
      (CumulativeGuidePruning.prefixMass (upperGuide leaf.cap leaf.blocks leaf.decode gamma) threshold : ℝ) / (gamma : ℝ) := by
    unfold lowerGuide
    rw [CumulativeGuidePruning.rationalFamily_prefix_real, lowerGuideAtoms_prefix, Rat.cast_div]
  have hgR : (0 : ℝ) < gamma := by exact_mod_cast (by linarith : (0 : ℚ) < gamma)
  have hU1 : ((∑ code : Fin (leaf.cap + 1), if (leaf.decode code.val : ℝ) ≤ threshold then labelMass leaf.blocks code.val else 0 : ℚ) : ℝ) ≤
      (CumulativeGuidePruning.prefixMass (upperGuide leaf.cap leaf.blocks leaf.decode gamma) threshold : ℝ) := Rat.cast_le.mpr hu.1
  have hU2 : (CumulativeGuidePruning.prefixMass (upperGuide leaf.cap leaf.blocks leaf.decode gamma) threshold : ℝ) ≤
      (gamma : ℝ) * ((∑ code : Fin (leaf.cap + 1), if (leaf.decode code.val : ℝ) ≤ threshold then labelMass leaf.blocks code.val else 0 : ℚ) : ℝ) := by
    rw [← Rat.cast_mul]
    exact Rat.cast_le.mpr hu.2
  rw [hGuide, hTrue]
  constructor
  · exact (div_le_iff₀ hgR).mpr (by simpa only [mul_comm] using hU2)
  · rw [mul_div_cancel₀ _ hgR.ne']
    exact hU1

theorem lowerLeaf_certified (leaf : ProposalLeaf) (gamma : ℚ) (hg : 1 ≤ gamma) :
    (RationalWeightedGuideTree.leaf leaf.family (leaf.lowerGuide gamma hg) gamma).real.LowerCertified := by
  apply WeightedGuideTree.leaf_lower_certified _ _ _ (by exact_mod_cast hg)
  · intro threshold; exact (leaf.lowerGuide_certificate gamma hg threshold).1
  · intro threshold; exact (leaf.lowerGuide_certificate gamma hg threshold).2

theorem lowerGuide_length_log_bound (leaf : ProposalLeaf) (delta : ℚ) (hd : 0 < delta) (hu : delta ≤ 1) :
    ((leaf.lowerGuideAtoms (1 + delta)).length : ℝ) ≤
      1 + 2 * Real.log ((totalMass leaf.blocks : ℝ) / (plateauPrefix leaf.cap leaf.blocks leaf.decode 0 : ℝ)) / (delta : ℝ) := by
  rw [leaf.lowerGuideAtoms_length]
  exact upperGuide_length_log_bound leaf.cap leaf.blocks leaf.partition leaf.positive leaf.decode leaf.monotone delta hd hu

theorem lowerGuideAtoms_positive (leaf : ProposalLeaf) (gamma : ℚ) (hg : 1 ≤ gamma) :
    ∀ atom ∈ leaf.lowerGuideAtoms gamma, 0 < atom.2 := by
  intro atom ha
  rcases List.mem_map.mp ha with ⟨source, hs, rfl⟩
  rcases List.mem_map.mp hs with ⟨bin, hb, rfl⟩
  exact div_pos (upperGuide_positive leaf.cap leaf.blocks leaf.partition leaf.positive leaf.decode leaf.monotone gamma hg 0 (by omega) bin hb) (by linarith)

end ProposalLeaf
end ImplicitLeafCounts
end Blotto
