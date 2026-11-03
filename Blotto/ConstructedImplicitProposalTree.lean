import Blotto.ImplicitCertifiedGuide
import Blotto.ImplicitRecursiveBitBudget
import Blotto.GuideAccuracyBudget

/-! Actual rebuilt implicit trees use scaled upper leaf bins and conservative
exact child-guide pair enumeration internally. Certificates and the uniform
factor budget are derived. Original leaf data, true Cartesian labels and their
resources are preserved; no R161 fast internal construction is claimed. -/

namespace Blotto
open scoped BigOperators Classical
namespace ImplicitLeafCounts
namespace ProposalTree

def rebuildGuides : ProposalTree → (gamma : ℚ) → (hg : 1 ≤ gamma) → ProposalTree
  | .leaf data _ _, gamma, hg => .leaf data (data.lowerGuide gamma hg) gamma
  | .fork _ _ left right, gamma, hg =>
    let leftNew := left.rebuildGuides gamma hg
    let rightNew := right.rebuildGuides gamma hg
    .fork (CumulativeInternalGuide.internalGuide leftNew.projected.guide rightNew.projected.guide gamma) gamma leftNew rightNew

theorem rationalGuides_convolution_real (left right : RationalWeightedGuideTree) (threshold : ℝ) :
    left.guide.real.convolution right.guide.real threshold = left.real.guide.convolution right.real.guide threshold := by
  cases left <;> cases right <;> rfl

theorem rebuild_certified (tree : ProposalTree) (gamma : ℚ) (hg : 1 ≤ gamma) :
    (tree.rebuildGuides gamma hg).projected.real.LowerCertified := by
  induction tree with
  | leaf data guide g => exact data.lowerLeaf_certified gamma hg
  | fork guide g left right ihL ihR =>
    let leftNew := left.rebuildGuides gamma hg
    let rightNew := right.rebuildGuides gamma hg
    apply WeightedGuideTree.fork_lower_certified _ _ _ _ (by exact_mod_cast hg) ihL ihR
    · intro threshold
      have he := (CumulativeInternalGuide.internalGuide_local_certificate leftNew.projected.guide rightNew.projected.guide gamma hg threshold).1
      rw [rationalGuides_convolution_real] at he
      exact he
    · intro threshold
      have he := (CumulativeInternalGuide.internalGuide_local_certificate leftNew.projected.guide rightNew.projected.guide gamma hg threshold).2
      rw [rationalGuides_convolution_real] at he
      exact he

theorem rebuild_trueSize (tree : ProposalTree) (gamma : ℚ) (hg : 1 ≤ gamma) :
    (tree.rebuildGuides gamma hg).projected.trueSize = tree.projected.trueSize := by
  induction tree with
  | leaf data guide g => rfl
  | fork guide g left right ihL ihR =>
    change (left.rebuildGuides gamma hg).projected.trueSize * (right.rebuildGuides gamma hg).projected.trueSize =
      left.projected.trueSize * right.projected.trueSize
    rw [ihL, ihR]

theorem rebuild_nodes (tree : ProposalTree) (gamma : ℚ) (hg : 1 ≤ gamma) :
    (tree.rebuildGuides gamma hg).projected.nodes = tree.projected.nodes := by
  induction tree with
  | leaf data guide g => rfl
  | fork guide g left right ihL ihR =>
    change 1 + (left.rebuildGuides gamma hg).projected.nodes + (right.rebuildGuides gamma hg).projected.nodes = _
    rw [ihL, ihR]
    rfl

theorem real_nodeCount (tree : ProposalTree) : tree.projected.real.nodeCount = tree.projected.nodes := by
  induction tree with
  | leaf data guide g => rfl
  | fork guide g left right ihL ihR =>
    change (left.projected.real.factors ++ right.projected.real.factors ++ [(g : ℝ)]).length = 1 + _ + _
    simp only [List.length_append, List.length_singleton]
    change left.projected.real.nodeCount + right.projected.real.nodeCount + 1 = _
    rw [ihL, ihR]
    omega

theorem rebuild_factors_same (tree : ProposalTree) (gamma : ℚ) (hg : 1 ≤ gamma) :
    ∀ factor ∈ (tree.rebuildGuides gamma hg).projected.real.factors, factor = (gamma : ℝ) := by
  induction tree with
  | leaf data guide g => intro factor hf; simpa only [rebuildGuides, projected, RationalWeightedGuideTree.real, WeightedGuideTree.factors, List.mem_singleton] using hf
  | fork guide g left right ihL ihR =>
    intro factor hf
    change factor ∈ (left.rebuildGuides gamma hg).projected.real.factors ++
      (right.rebuildGuides gamma hg).projected.real.factors ++ [(gamma : ℝ)] at hf
    simp only [List.mem_append, List.mem_singleton] at hf
    rcases hf with (hl | hr) | he
    · exact ihL factor hl
    · exact ihR factor hr
    · exact he

def constructionGamma (tree : ProposalTree) : ℚ := 1 + 1 / (8 * (tree.projected.nodes : ℚ))

theorem nodes_positive (tree : ProposalTree) : 0 < tree.projected.nodes := by
  induction tree with
  | leaf data guide g => exact Nat.zero_lt_one
  | fork guide g left right ihL ihR => change 0 < 1 + _ + _; omega

theorem constructionGamma_ge_one (tree : ProposalTree) : 1 ≤ tree.constructionGamma := by
  have hn : (0 : ℚ) < tree.projected.nodes := by exact_mod_cast tree.nodes_positive
  unfold constructionGamma
  have hp : (0 : ℚ) ≤ 1 / (8 * (tree.projected.nodes : ℚ)) := by positivity
  linarith

def constructed (tree : ProposalTree) : ProposalTree := tree.rebuildGuides tree.constructionGamma tree.constructionGamma_ge_one

theorem constructed_certified (tree : ProposalTree) : tree.constructed.projected.real.LowerCertified :=
  tree.rebuild_certified tree.constructionGamma tree.constructionGamma_ge_one

theorem constructed_factor (tree : ProposalTree) : tree.constructed.projected.factor ≤ 8 / 7 := by
  have he : tree.constructed.projected.real.factor ≤ 8 / 7 := by
    apply WeightedGuideTree.uniform_factor_bound _ tree.constructed_certified
    intro factor hf
    have hEq := tree.rebuild_factors_same tree.constructionGamma tree.constructionGamma_ge_one factor hf
    rw [hEq]
    rw [tree.constructed.real_nodeCount]
    unfold constructed
    rw [rebuild_nodes]
    unfold constructionGamma
    simp only [Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat]
    exact le_rfl
  rw [← RationalWeightedGuideTree.factor_real] at he
  have hCast : ((8 / 7 : ℚ) : ℝ) = 8 / 7 := by norm_num
  rw [← hCast] at he
  exact Rat.cast_le.mp he

theorem constructed_factorCeiling (tree : ProposalTree) : rationalFactorCeiling tree.constructed.projected.factor ≤ 2 :=
  rationalFactorCeiling_le_two _ (by linarith [tree.constructed_factor])

theorem constructed_attempts (tree : ProposalTree) (E : ℕ) :
    tree.constructed.projected.scheduledAttempts E ≤ 2 * (E + 1) := by
  unfold RationalWeightedGuideTree.scheduledAttempts rejectionScheduleAttempts
  exact Nat.mul_le_mul_right _ tree.constructed_factorCeiling

theorem rebuild_real_trueSize (tree : ProposalTree) (gamma : ℚ) (hg : 1 ≤ gamma) :
    (tree.rebuildGuides gamma hg).projected.real.trueSize = tree.projected.real.trueSize :=
  (tree.rebuildGuides gamma hg).projected.real_trueSize.trans
    ((tree.rebuild_trueSize gamma hg).trans tree.projected.real_trueSize.symm)

theorem rebuild_true_resource_mass (tree : ProposalTree) (gamma : ℚ) (hg : 1 ≤ gamma)
    (label : Fin tree.projected.real.trueSize) :
    (tree.rebuildGuides gamma hg).projected.real.trueFamily.resource (label.cast (tree.rebuild_real_trueSize gamma hg).symm) =
      tree.projected.real.trueFamily.resource label ∧
    (tree.rebuildGuides gamma hg).projected.real.trueFamily.mass (label.cast (tree.rebuild_real_trueSize gamma hg).symm) =
      tree.projected.real.trueFamily.mass label := by
  induction tree with
  | leaf data guide g => exact ⟨rfl, rfl⟩
  | fork guide g left right ihL ihR =>
    let pair := finProdFinEquiv.symm label
    have hp : finProdFinEquiv
        (pair.1.cast (left.rebuild_real_trueSize gamma hg).symm, pair.2.cast (right.rebuild_real_trueSize gamma hg).symm) =
        label.cast ((fork guide g left right).rebuild_real_trueSize gamma hg).symm := by
      apply Fin.ext
      have hLabel := congrArg Fin.val (Equiv.apply_symm_apply finProdFinEquiv label)
      simp only [finProdFinEquiv_apply_val, Fin.val_cast] at hLabel ⊢
      rw [right.rebuild_real_trueSize gamma hg]
      exact hLabel
    have hPair : finProdFinEquiv.symm (label.cast ((fork guide g left right).rebuild_real_trueSize gamma hg).symm) =
        (pair.1.cast (left.rebuild_real_trueSize gamma hg).symm, pair.2.cast (right.rebuild_real_trueSize gamma hg).symm) := by
      exact (Equiv.symm_apply_apply finProdFinEquiv _).symm.trans
        (congrArg (fun index => finProdFinEquiv.symm index) hp) |>.symm
    have hL := ihL pair.1
    have hR := ihR pair.2
    constructor
    · change (left.rebuildGuides gamma hg).projected.real.trueFamily.resource
          (finProdFinEquiv.symm (label.cast ((fork guide g left right).rebuild_real_trueSize gamma hg).symm)).1 +
        (right.rebuildGuides gamma hg).projected.real.trueFamily.resource
          (finProdFinEquiv.symm (label.cast ((fork guide g left right).rebuild_real_trueSize gamma hg).symm)).2 = _
      have he := congrArg (fun labels =>
        (left.rebuildGuides gamma hg).projected.real.trueFamily.resource labels.1 +
        (right.rebuildGuides gamma hg).projected.real.trueFamily.resource labels.2) hPair
      exact he.trans (congrArg₂ (· + ·) hL.1 hR.1)
    · change (left.rebuildGuides gamma hg).projected.real.trueFamily.mass
          (finProdFinEquiv.symm (label.cast ((fork guide g left right).rebuild_real_trueSize gamma hg).symm)).1 *
        (right.rebuildGuides gamma hg).projected.real.trueFamily.mass
          (finProdFinEquiv.symm (label.cast ((fork guide g left right).rebuild_real_trueSize gamma hg).symm)).2 = _
      have he := congrArg (fun labels =>
        (left.rebuildGuides gamma hg).projected.real.trueFamily.mass labels.1 *
        (right.rebuildGuides gamma hg).projected.real.trueFamily.mass labels.2) hPair
      exact he.trans (congrArg₂ (· * ·) hL.2 hR.2)

theorem rebuild_true_prefix (tree : ProposalTree) (gamma : ℚ) (hg : 1 ≤ gamma) (budget : ℝ) :
    (tree.rebuildGuides gamma hg).projected.real.trueFamily.prefixMass budget =
      tree.projected.real.trueFamily.prefixMass budget := by
  unfold WeightedResourceFamily.prefixMass
  rw [← Equiv.sum_comp (finCongr (tree.rebuild_real_trueSize gamma hg).symm)]
  apply Finset.sum_congr rfl
  intro label _
  have he := tree.rebuild_true_resource_mass gamma hg label
  simp only [finCongr_apply, he.1, he.2]

end ProposalTree
end ImplicitLeafCounts
end Blotto
