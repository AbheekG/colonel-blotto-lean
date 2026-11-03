import Blotto.ImplicitInternalGuideSize
import Blotto.ConstructedImplicitPreservation
import Blotto.ImplicitResourcePrefix
import Blotto.ImplicitZeroFallback

/-! Retained guides of the actual conservative recursive constructor have
additive logarithmic mass ranges. Internal pruning preserves the complete zero
prefix and decreases total mass. Pair enumeration remains preparation work;
this module bounds stored support without an exponential Cartesian recursion. -/

namespace Blotto
open scoped BigOperators Classical
namespace ImplicitLeafCounts
open CumulativeInternalGuide CumulativeGuidePruning CumulativeGuideSorting

theorem rationalFamily_prefix_zero (atoms : List Atom) (hn : CumulativeGuidePruning.Nonnegative atoms) :
    (rationalFamily atoms hn).prefixMass 0 = CumulativeGuidePruning.prefixMass atoms 0 := by
  rw [prefixMass_eq_sum]
  unfold RationalWeightedFamily.prefixMass rationalFamily
  apply Finset.sum_congr rfl
  intro label _
  have hc : (atoms[label].1 : ℝ) ≤ 0 ↔ atoms[label].1 ≤ 0 := by norm_cast
  simp only [hc]

theorem pruned_resources_nonnegative (atoms : List Atom) (gamma : ℚ)
    (hr : ∀ atom ∈ atoms, 0 ≤ atom.1) : ∀ atom ∈ guideAtoms atoms gamma, 0 ≤ atom.1 := by
  intro atom ha
  have hm : atom.1 ∈ (CumulativeResourceGrouping.group (sort atoms)).map Prod.fst :=
    (scan_resources_sublist _ gamma 0 0).subset (List.mem_map.mpr ⟨atom, ha, rfl⟩)
  rcases List.mem_map.mp hm with ⟨source, hs, he⟩
  rw [← he]
  exact CumulativeResourceGrouping.group_resources_nonnegative (sort atoms) (sort_resources_nonnegative atoms hr) source hs

namespace ProposalLeaf

theorem lowerGuide_total (leaf : ProposalLeaf) (gamma : ℚ) (hg : 1 ≤ gamma) :
    familyTotal (leaf.lowerGuide gamma hg) = totalMass leaf.blocks / gamma := by
  unfold lowerGuide
  rw [rationalFamily_total]
  unfold lowerGuideAtoms CumulativeGuidePruning.totalMass
  rw [List.map_map]
  simp only [Function.comp_def]
  have he : ∀ atoms : List Atom, (atoms.map (fun atom => atom.2 / gamma)).sum =
      (atoms.map Prod.snd).sum / gamma := by
    intro atoms
    induction atoms with
    | nil => simp
    | cons atom rest ih => simp only [List.map_cons, List.sum_cons]; rw [ih]; ring
  rw [he]
  change CumulativeGuidePruning.totalMass (upperGuide leaf.cap leaf.blocks leaf.decode gamma) / gamma = _
  rw [upperGuide_totalMass leaf.cap leaf.blocks leaf.partition leaf.positive leaf.decode leaf.monotone gamma hg]

theorem lowerGuide_resources (leaf : ProposalLeaf) (gamma : ℚ) (hg : 1 ≤ gamma)
    (hn : ∀ code : Fin (leaf.cap + 1), 0 ≤ leaf.decode code.val) :
    ∀ label, 0 ≤ (leaf.lowerGuide gamma hg).resource label := by
  intro label
  unfold lowerGuide rationalFamily
  have ha := List.getElem_mem label.isLt
  rcases List.mem_map.mp ha with ⟨source, hs, hEq⟩
  rcases List.mem_map.mp hs with ⟨bin, hb, rfl⟩
  have hc := localUpperBins_after leaf.cap leaf.blocks leaf.decode gamma
    (upperBins leaf.cap leaf.blocks leaf.decode gamma 0) 0
    (upperBins_local leaf.cap leaf.blocks leaf.partition leaf.positive leaf.decode leaf.monotone gamma hg 0 (by omega)) bin hb
  have he := congrArg Prod.fst hEq
  change 0 ≤ (leaf.lowerGuideAtoms gamma)[label].1
  have hPositive : 0 ≤ bin.resource := by rw [hc.2.2.2]; exact hn ⟨bin.lo, by omega⟩
  exact he ▸ hPositive

theorem lowerGuide_zero_lower (leaf : ProposalLeaf) (gamma : ℚ) (hg : 1 ≤ gamma)
    (hzero : leaf.decode 0 = 0) :
    prefixMass leaf.blocks 0 / gamma ≤ (leaf.lowerGuide gamma hg).prefixMass 0 := by
  have hUpper := upperGuide_envelope leaf.cap leaf.blocks leaf.partition leaf.positive leaf.decode leaf.monotone gamma hg 0
  have hFamily : leaf.family.prefixMass 0 =
      ∑ code : Fin (leaf.cap + 1), if (leaf.decode code.val : ℝ) ≤ 0 then labelMass leaf.blocks code.val else 0 := by
    unfold ProposalLeaf.family decodedFamily RationalWeightedFamily.prefixMass
    apply Finset.sum_congr rfl
    intro code _
    have hc : (leaf.decode code.val : ℝ) ≤ 0 ↔ leaf.decode code.val ≤ 0 := by norm_cast
    simp only [hc]
  have hFirst : prefixMass leaf.blocks 0 ≤ leaf.family.prefixMass 0 := by
    rw [partition_prefix_zero leaf.cap leaf.blocks leaf.partition]
    unfold RationalWeightedFamily.prefixMass family decodedFamily
    change labelMass leaf.blocks 0 ≤ ∑ code : Fin (leaf.cap + 1),
      if leaf.decode code.val ≤ 0 then labelMass leaf.blocks code.val else 0
    have hb := Finset.single_le_sum (s := Finset.univ)
      (f := fun code : Fin (leaf.cap + 1) => if leaf.decode code.val ≤ 0 then labelMass leaf.blocks code.val else 0)
      (fun code _ => by split_ifs; exact (partition_labelMass_positive leaf.cap leaf.blocks leaf.partition leaf.positive code).le; exact le_rfl)
      (Finset.mem_univ (⟨0, by omega⟩ : Fin (leaf.cap + 1)))
    simpa only [hzero, le_refl, ite_true] using hb
  have hGuide : (leaf.lowerGuide gamma hg).prefixMass 0 =
      CumulativeGuidePruning.prefixMass (upperGuide leaf.cap leaf.blocks leaf.decode gamma) 0 / gamma := by
    unfold lowerGuide
    rw [rationalFamily_prefix_zero, leaf.lowerGuideAtoms_prefix]
  rw [hGuide]
  exact div_le_div_of_nonneg_right (hFirst.trans (by rw [hFamily]; exact hUpper.1)) (by linarith)

end ProposalLeaf

namespace ProposalTree

def leafTotal : ProposalTree → ℚ
  | .leaf data _ _ => totalMass data.blocks
  | .fork _ _ left right => left.leafTotal * right.leafTotal

def leafZero : ProposalTree → ℚ
  | .leaf data _ _ => prefixMass data.blocks 0
  | .fork _ _ left right => left.leafZero * right.leafZero

noncomputable def leafRange : ProposalTree → ℝ
  | .leaf data _ _ => Real.log ((totalMass data.blocks : ℝ) / (prefixMass data.blocks 0 : ℝ))
  | .fork _ _ left right => left.leafRange + right.leafRange

theorem leafTotal_positive (tree : ProposalTree) : 0 < tree.leafTotal := by
  induction tree with
  | leaf data guide gamma =>
    change 0 < totalMass data.blocks
    rw [← partition_prefixMass_full data.cap data.blocks data.partition (data.cap : ℤ) le_rfl]
    exact partition_prefixMass_positive data.cap data.blocks data.partition data.positive _ (by omega)
  | fork guide gamma left right ihL ihR => exact mul_pos ihL ihR

theorem leafZero_positive (tree : ProposalTree) : 0 < tree.leafZero := by
  induction tree with
  | leaf data guide gamma => exact partition_prefixMass_positive data.cap data.blocks data.partition data.positive 0 le_rfl
  | fork guide gamma left right ihL ihR => exact mul_pos ihL ihR

theorem rebuild_guide_resources (tree : ProposalTree) (hn : tree.NonnegativeResources) (gamma : ℚ) (hg : 1 ≤ gamma) :
    ∀ label, 0 ≤ (tree.rebuildGuides gamma hg).projected.guide.resource label := by
  induction tree with
  | leaf data guide g => exact data.lowerGuide_resources gamma hg hn
  | fork guide g left right ihL ihR =>
    intro label
    let atoms := pairAtoms (left.rebuildGuides gamma hg).projected.guide (right.rebuildGuides gamma hg).projected.guide
    have hr := pairAtoms_resources_nonnegative _ _ (ihL hn.1) (ihR hn.2)
    have hp := pruned_resources_nonnegative atoms gamma hr
    exact hp _ (List.getElem_mem label.isLt)

theorem rebuild_total_zero (tree : ProposalTree) (hn : tree.NonnegativeResources) (hz : tree.ZeroResources)
    (gamma : ℚ) (hg : 1 ≤ gamma) :
    familyTotal (tree.rebuildGuides gamma hg).projected.guide ≤ tree.leafTotal / gamma ^ tree.leaves ∧
      tree.leafZero / gamma ^ tree.leaves ≤ (tree.rebuildGuides gamma hg).projected.guide.prefixMass 0 := by
  induction tree with
  | leaf data guide g =>
    simp only [rebuildGuides, projected, RationalWeightedGuideTree.guide, leaves, pow_one, leafTotal, leafZero]
    exact ⟨le_of_eq (data.lowerGuide_total gamma hg), data.lowerGuide_zero_lower gamma hg hz⟩
  | fork guide g left right ihL ihR =>
    have hL := ihL hn.1 hz.1
    have hR := ihR hn.2 hz.2
    have hg0 : 0 < gamma := by linarith
    have hZeroL : 0 < (left.rebuildGuides gamma hg).projected.guide.prefixMass 0 :=
      (div_pos left.leafZero_positive (pow_pos hg0 _)).trans_le hL.2
    have hZeroR : 0 < (right.rebuildGuides gamma hg).projected.guide.prefixMass 0 :=
      (div_pos right.leafZero_positive (pow_pos hg0 _)).trans_le hR.2
    constructor
    · have he := internalGuide_total_bound (left.rebuildGuides gamma hg).projected.guide
        (right.rebuildGuides gamma hg).projected.guide gamma hg
      have hProd := mul_le_mul hL.1 hR.1
        (by apply Finset.sum_nonneg; intro i _; exact (right.rebuildGuides gamma hg).projected.guide.mass_nonnegative i)
        (div_nonneg left.leafTotal_positive.le (pow_pos hg0 _).le)
      change familyTotal (internalGuide _ _ gamma) ≤ _
      exact he.trans (by simpa only [leafTotal, leaves, pow_add, div_mul_div_comm] using hProd)
    · change _ ≤ (internalGuide _ _ gamma).prefixMass 0
      rw [internalGuide_zero _ _ (left.rebuild_guide_resources hn.1 gamma hg) (right.rebuild_guide_resources hn.2 gamma hg) hZeroL hZeroR gamma hg]
      have hProd := mul_le_mul hL.2 hR.2 (div_pos right.leafZero_positive (pow_pos hg0 _)).le hZeroL.le
      simpa only [leafZero, leaves, pow_add, div_mul_div_comm] using hProd

theorem leafZero_le_total (tree : ProposalTree) : tree.leafZero ≤ tree.leafTotal := by
  induction tree with
  | leaf data guide g =>
    have hm := prefixMass_mono data.blocks (fun block hb => (data.positive block hb).le)
      (show (0 : ℤ) ≤ (data.cap : ℤ) by omega)
    rw [partition_prefixMass_full data.cap data.blocks data.partition (data.cap : ℤ) le_rfl] at hm
    exact hm
  | fork guide g left right ihL ihR =>
    exact mul_le_mul ihL ihR right.leafZero_positive.le left.leafTotal_positive.le

theorem leafRange_eq_log (tree : ProposalTree) : tree.leafRange = Real.log ((tree.leafTotal : ℝ) / (tree.leafZero : ℝ)) := by
  induction tree with
  | leaf data guide g => rfl
  | fork guide g left right ihL ihR =>
    change left.leafRange + right.leafRange = Real.log (((left.leafTotal * right.leafTotal : ℚ) : ℝ) /
      ((left.leafZero * right.leafZero : ℚ) : ℝ))
    rw [ihL, ihR, Rat.cast_mul, Rat.cast_mul, ← div_mul_div_comm,
      Real.log_mul (by exact_mod_cast ne_of_gt (div_pos left.leafTotal_positive left.leafZero_positive))
        (by exact_mod_cast ne_of_gt (div_pos right.leafTotal_positive right.leafZero_positive))]

theorem leafRange_nonnegative (tree : ProposalTree) : 0 ≤ tree.leafRange := by
  rw [tree.leafRange_eq_log]
  have hf : (0 : ℝ) < tree.leafZero := by exact_mod_cast tree.leafZero_positive
  have hMass : (tree.leafZero : ℝ) ≤ tree.leafTotal := by exact_mod_cast tree.leafZero_le_total
  exact Real.log_nonneg ((one_le_div hf).mpr hMass)

theorem rebuild_log_range (tree : ProposalTree) (hn : tree.NonnegativeResources) (hz : tree.ZeroResources)
    (gamma : ℚ) (hg : 1 ≤ gamma) :
    Real.log ((familyTotal (tree.rebuildGuides gamma hg).projected.guide : ℝ) /
      ((tree.rebuildGuides gamma hg).projected.guide.prefixMass 0 : ℝ)) ≤ tree.leafRange := by
  have hBounds := tree.rebuild_total_zero hn hz gamma hg
  have hg0 : 0 < gamma := by linarith
  have hZero : 0 < (tree.rebuildGuides gamma hg).projected.guide.prefixMass 0 :=
    (div_pos tree.leafZero_positive (pow_pos hg0 _)).trans_le hBounds.2
  have hZeroR : (0 : ℝ) < (tree.rebuildGuides gamma hg).projected.guide.prefixMass 0 := by exact_mod_cast hZero
  have hTotal : 0 < familyTotal (tree.rebuildGuides gamma hg).projected.guide := by
    have hPrefixLe : (tree.rebuildGuides gamma hg).projected.guide.prefixMass 0 ≤ familyTotal (tree.rebuildGuides gamma hg).projected.guide := by
      apply Finset.sum_le_sum
      intro label _
      split_ifs
      · exact le_rfl
      · exact (tree.rebuildGuides gamma hg).projected.guide.mass_nonnegative label
    exact hZero.trans_le hPrefixLe
  have hRatio : familyTotal (tree.rebuildGuides gamma hg).projected.guide /
      (tree.rebuildGuides gamma hg).projected.guide.prefixMass 0 ≤ tree.leafTotal / tree.leafZero := by
    have hb := div_le_div₀ (div_pos tree.leafTotal_positive (pow_pos hg0 _)).le hBounds.1
      (div_pos tree.leafZero_positive (pow_pos hg0 _)) hBounds.2
    have hCancel : (tree.leafTotal / gamma ^ tree.leaves) / (tree.leafZero / gamma ^ tree.leaves) = tree.leafTotal / tree.leafZero := by
      field_simp [ne_of_gt tree.leafZero_positive, pow_ne_zero _ hg0.ne']
    exact hb.trans_eq hCancel
  rw [tree.leafRange_eq_log]
  exact Real.log_le_log (by exact_mod_cast div_pos hTotal hZero) (by exact_mod_cast hRatio)

theorem rebuild_pair_log_range (left right : ProposalTree) (hnL : left.NonnegativeResources) (hnR : right.NonnegativeResources)
    (hzL : left.ZeroResources) (hzR : right.ZeroResources) (gamma : ℚ) (hg : 1 ≤ gamma) :
    Real.log (((familyTotal (left.rebuildGuides gamma hg).projected.guide *
      familyTotal (right.rebuildGuides gamma hg).projected.guide : ℚ) : ℝ) /
      (((left.rebuildGuides gamma hg).projected.guide.prefixMass 0 *
        (right.rebuildGuides gamma hg).projected.guide.prefixMass 0 : ℚ) : ℝ)) ≤ left.leafRange + right.leafRange := by
  have hL := left.rebuild_total_zero hnL hzL gamma hg
  have hR := right.rebuild_total_zero hnR hzR gamma hg
  have hg0 : 0 < gamma := by linarith
  have hpL : 0 < (left.rebuildGuides gamma hg).projected.guide.prefixMass 0 :=
    (div_pos left.leafZero_positive (pow_pos hg0 _)).trans_le hL.2
  have hpR : 0 < (right.rebuildGuides gamma hg).projected.guide.prefixMass 0 :=
    (div_pos right.leafZero_positive (pow_pos hg0 _)).trans_le hR.2
  have hTotL : 0 < familyTotal (left.rebuildGuides gamma hg).projected.guide := by
    have he : (left.rebuildGuides gamma hg).projected.guide.prefixMass 0 ≤ familyTotal (left.rebuildGuides gamma hg).projected.guide := by
      apply Finset.sum_le_sum; intro label _; split_ifs; exact le_rfl; exact (left.rebuildGuides gamma hg).projected.guide.mass_nonnegative label
    exact hpL.trans_le he
  have hTotR : 0 < familyTotal (right.rebuildGuides gamma hg).projected.guide := by
    have he : (right.rebuildGuides gamma hg).projected.guide.prefixMass 0 ≤ familyTotal (right.rebuildGuides gamma hg).projected.guide := by
      apply Finset.sum_le_sum; intro label _; split_ifs; exact le_rfl; exact (right.rebuildGuides gamma hg).projected.guide.mass_nonnegative label
    exact hpR.trans_le he
  rw [Rat.cast_mul, Rat.cast_mul, ← div_mul_div_comm,
    Real.log_mul (by exact_mod_cast ne_of_gt (div_pos hTotL hpL)) (by exact_mod_cast ne_of_gt (div_pos hTotR hpR))]
  exact add_le_add (left.rebuild_log_range hnL hzL gamma hg) (right.rebuild_log_range hnR hzR gamma hg)

theorem rebuild_guideSize_bound (tree : ProposalTree) (hn : tree.NonnegativeResources) (hz : tree.ZeroResources)
    (delta : ℚ) (hd : 0 < delta) (hu : delta ≤ 1) :
    ((tree.rebuildGuides (1 + delta) (by linarith)).projected.guideSize : ℝ) ≤
      1 + 2 * tree.leafRange / (delta : ℝ) := by
  have hg : 1 ≤ 1 + delta := by linarith
  cases tree with
  | leaf data guide g =>
    have hSize := data.lowerGuide_length_log_bound delta hd hu
    have hPlateau := plateauPrefix_log_range data.cap data.blocks data.partition data.positive data.decode data.monotone
    have hdR : (0 : ℝ) ≤ delta := by exact_mod_cast hd.le
    exact hSize.trans (add_le_add_right (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hPlateau (by norm_num : (0 : ℝ) ≤ 2)) hdR) 1)
  | fork guide g left right =>
    have hL := left.rebuild_total_zero hn.1 hz.1 (1 + delta) hg
    have hR := right.rebuild_total_zero hn.2 hz.2 (1 + delta) hg
    have hg0 : 0 < 1 + delta := by linarith
    have hpL := (div_pos left.leafZero_positive (pow_pos hg0 _)).trans_le hL.2
    have hpR := (div_pos right.leafZero_positive (pow_pos hg0 _)).trans_le hR.2
    have hSize := internalGuide_length_log_bound (left.rebuildGuides (1 + delta) hg).projected.guide
      (right.rebuildGuides (1 + delta) hg).projected.guide (left.rebuild_guide_resources hn.1 _ hg)
      (right.rebuild_guide_resources hn.2 _ hg) hpL hpR delta hd hu
    have hLog := rebuild_pair_log_range left right hn.1 hn.2 hz.1 hz.2 (1 + delta) hg
    have hdR : (0 : ℝ) ≤ delta := by exact_mod_cast hd.le
    exact hSize.trans (add_le_add_right (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hLog (by norm_num : (0 : ℝ) ≤ 2)) hdR) 1)

def AllGuideSizes (bound : ℝ) : ProposalTree → Prop
  | .leaf data guide gamma => ((RationalWeightedGuideTree.leaf data.family guide gamma).guideSize : ℝ) ≤ bound
  | .fork guide gamma left right => ((RationalWeightedGuideTree.fork guide gamma left.projected right.projected).guideSize : ℝ) ≤ bound ∧
      left.AllGuideSizes bound ∧ right.AllGuideSizes bound

theorem AllGuideSizes.mono (tree : ProposalTree) {first last : ℝ} (h : tree.AllGuideSizes first) (hb : first ≤ last) :
    tree.AllGuideSizes last := by
  induction tree with
  | leaf data guide gamma => exact h.trans hb
  | fork guide gamma left right ihL ihR => exact ⟨h.1.trans hb, ihL h.2.1, ihR h.2.2⟩

theorem rebuild_allGuideSizes (tree : ProposalTree) (hn : tree.NonnegativeResources) (hz : tree.ZeroResources)
    (delta : ℚ) (hd : 0 < delta) (hu : delta ≤ 1) :
    (tree.rebuildGuides (1 + delta) (by linarith)).AllGuideSizes (1 + 2 * tree.leafRange / (delta : ℝ)) := by
  induction tree with
  | leaf data guide g => exact rebuild_guideSize_bound _ hn hz delta hd hu
  | fork guide g left right ihL ihR =>
    have hRoot := rebuild_guideSize_bound (fork guide g left right) hn hz delta hd hu
    have hdR : (0 : ℝ) ≤ delta := by exact_mod_cast hd.le
    have hLeft : 1 + 2 * left.leafRange / (delta : ℝ) ≤ 1 + 2 * (left.leafRange + right.leafRange) / (delta : ℝ) :=
      add_le_add_right (div_le_div_of_nonneg_right (by linarith [right.leafRange_nonnegative]) hdR) 1
    have hRight : 1 + 2 * right.leafRange / (delta : ℝ) ≤ 1 + 2 * (left.leafRange + right.leafRange) / (delta : ℝ) :=
      add_le_add_right (div_le_div_of_nonneg_right (by linarith [left.leafRange_nonnegative]) hdR) 1
    exact ⟨hRoot, AllGuideSizes.mono (left.rebuildGuides _ _) (ihL hn.1 hz.1) hLeft,
      AllGuideSizes.mono (right.rebuildGuides _ _) (ihR hn.2 hz.2) hRight⟩

def maximumBlocks : ProposalTree → ℕ
  | .leaf data _ _ => data.blocks.length - 1
  | .fork _ _ left right => max left.maximumBlocks right.maximumBlocks

def maximumWidth : ProposalTree → ℕ
  | .leaf data _ _ => offsetWidth data.cap
  | .fork _ _ left right => max left.maximumWidth right.maximumWidth

theorem rebuild_maximumBlocks (tree : ProposalTree) (gamma : ℚ) (hg : 1 ≤ gamma) :
    (tree.rebuildGuides gamma hg).maximumBlocks = tree.maximumBlocks := by
  induction tree with
  | leaf data guide g => rfl
  | fork guide g left right ihL ihR => simp only [rebuildGuides, maximumBlocks, ihL, ihR]

theorem rebuild_maximumWidth (tree : ProposalTree) (gamma : ℚ) (hg : 1 ≤ gamma) :
    (tree.rebuildGuides gamma hg).maximumWidth = tree.maximumWidth := by
  induction tree with
  | leaf data guide g => rfl
  | fork guide g left right ihL ihR => simp only [rebuildGuides, maximumWidth, ihL, ihR]

theorem structuralCaps_of_allGuideSizes (tree : ProposalTree) (bound : ℕ) (h : tree.AllGuideSizes (bound : ℝ)) :
    tree.StructuralCaps tree.maximumBlocks tree.maximumWidth bound := by
  induction tree with
  | leaf data guide gamma => exact ⟨le_rfl, le_rfl⟩
  | fork guide gamma left right ihL ihR =>
    have hGuide : left.projected.guideSize ≤ bound := by
      have hLeft : (left.projected.guideSize : ℝ) ≤ bound := by
        cases left with
        | leaf data guide gamma => exact h.2.1
        | fork guide gamma l r => exact h.2.1.1
      exact_mod_cast hLeft
    have hL := ihL h.2.1
    have hR := ihR h.2.2
    have hMono : ∀ subtree : ProposalTree, ∀ (b w p b' w' : ℕ), subtree.StructuralCaps b w p → b ≤ b' → w ≤ w' → subtree.StructuralCaps b' w' p := by
      intro subtree
      induction subtree with
      | leaf data guide gamma => intro b w p b' w' hs hb hw; exact ⟨hs.1.trans hb, hs.2.trans hw⟩
      | fork guide gamma l r ihL ihR => intro b w p b' w' hs hb hw; exact ⟨hs.1, ihL _ _ _ _ _ hs.2.1 hb hw, ihR _ _ _ _ _ hs.2.2 hb hw⟩
    exact ⟨by omega, hMono left _ _ _ _ _ hL (Nat.le_max_left _ _) (Nat.le_max_left _ _),
      hMono right _ _ _ _ _ hR (Nat.le_max_right _ _) (Nat.le_max_right _ _)⟩

def guideCountCap (range delta : ℚ) : ℕ := rationalFactorCeiling (1 + 2 * range / delta)

theorem rebuild_structuralCaps (tree : ProposalTree) (hn : tree.NonnegativeResources) (hz : tree.ZeroResources)
    (delta : ℚ) (hd : 0 < delta) (hu : delta ≤ 1) (range : ℚ) (hRange : tree.leafRange ≤ (range : ℝ)) :
    (tree.rebuildGuides (1 + delta) (by linarith)).StructuralCaps
      tree.maximumBlocks tree.maximumWidth (guideCountCap range delta) := by
  have hRange0 : 0 ≤ range := by
    have hR : (0 : ℝ) ≤ (range : ℝ) := tree.leafRange_nonnegative.trans hRange
    exact_mod_cast hR
  have hCeil := rationalFactorCeiling_bound (1 + 2 * range / delta) (by positivity)
  have hCeilR : (1 : ℝ) + 2 * (range : ℝ) / (delta : ℝ) ≤ (guideCountCap range delta : ℝ) := by
    unfold guideCountCap
    exact_mod_cast hCeil
  have hBound : 1 + 2 * tree.leafRange / (delta : ℝ) ≤ (guideCountCap range delta : ℝ) :=
    (add_le_add_right (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hRange (by norm_num)) (by exact_mod_cast hd.le)) 1).trans hCeilR
  have hs := AllGuideSizes.mono (tree.rebuildGuides (1 + delta) (by linarith))
    (tree.rebuild_allGuideSizes hn hz delta hd hu) hBound
  have hc := (tree.rebuildGuides (1 + delta) (by linarith)).structuralCaps_of_allGuideSizes _ hs
  rw [tree.rebuild_maximumBlocks, tree.rebuild_maximumWidth] at hc
  exact hc

end ProposalTree
end ImplicitLeafCounts
end Blotto
