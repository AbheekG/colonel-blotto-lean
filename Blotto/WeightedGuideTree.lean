import Blotto.WeightedPrefixConvolution

/-! The explicit local lower-guide certificates of R160 imply a whole-tree
envelope. The true family is the Cartesian product of labelled leaf states;
equal resources remain distinct. No guide construction or proposal algorithm
is asserted by these semantic definitions. -/

namespace Blotto
open scoped BigOperators Classical

namespace WeightedResourceFamily

noncomputable def product {n m : ℕ} (a : WeightedResourceFamily n)
    (b : WeightedResourceFamily m) : WeightedResourceFamily (n * m) :=
  ⟨fun k => a.resource (finProdFinEquiv.symm k).1 + b.resource (finProdFinEquiv.symm k).2,
    fun k => a.mass (finProdFinEquiv.symm k).1 * b.mass (finProdFinEquiv.symm k).2,
    fun _ => mul_nonneg (a.mass_nonnegative _) (b.mass_nonnegative _)⟩

theorem product_resource {n m : ℕ} (a : WeightedResourceFamily n)
    (b : WeightedResourceFamily m) (i : Fin n) (j : Fin m) :
    (a.product b).resource (finProdFinEquiv (i, j)) = a.resource i + b.resource j := by
  change a.resource (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1 +
    b.resource (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = _
  rw [Equiv.symm_apply_apply]

theorem product_mass {n m : ℕ} (a : WeightedResourceFamily n)
    (b : WeightedResourceFamily m) (i : Fin n) (j : Fin m) :
    (a.product b).mass (finProdFinEquiv (i, j)) = a.mass i * b.mass j := by
  change a.mass (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1 *
    b.mass (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = _
  rw [Equiv.symm_apply_apply]

theorem product_prefix {n m : ℕ} (a : WeightedResourceFamily n)
    (b : WeightedResourceFamily m) (t : ℝ) :
    (a.product b).prefixMass t = a.convolution b t := by
  unfold prefixMass convolution product
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply]
  exact Fintype.sum_prod_type _

theorem prefix_positive_iff_exists {n : ℕ} (a : WeightedResourceFamily n) (t : ℝ) :
    0 < a.prefixMass t ↔ ∃ i, a.resource i ≤ t ∧ 0 < a.mass i := by
  have hn : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ if a.resource i ≤ t then a.mass i else 0 := by
    intro i _
    split_ifs
    · exact a.mass_nonnegative i
    · exact le_rfl
  rw [prefixMass, Finset.sum_pos_iff_of_nonneg hn]
  constructor
  · rintro ⟨i, _, hi⟩
    by_cases hr : a.resource i ≤ t
    · exact ⟨i, hr, by simpa only [hr, ite_true] using hi⟩
    · simp only [hr, ite_false, lt_self_iff_false] at hi
  · rintro ⟨i, hr, hi⟩
    exact ⟨i, Finset.mem_univ i, by simpa only [hr, ite_true] using hi⟩

end WeightedResourceFamily

inductive WeightedGuideTree where
  | leaf {n p : ℕ} (trueFamily : WeightedResourceFamily n)
      (guide : WeightedResourceFamily p) (gamma : ℝ)
  | fork {p : ℕ} (guide : WeightedResourceFamily p) (gamma : ℝ)
      (left right : WeightedGuideTree)

namespace WeightedGuideTree

def trueSize : WeightedGuideTree → ℕ
  | .leaf (n := n) _ _ _ => n
  | .fork _ _ left right => left.trueSize * right.trueSize

def guideSize : WeightedGuideTree → ℕ
  | .leaf (p := p) _ _ _ => p
  | .fork (p := p) _ _ _ _ => p

noncomputable def trueFamily : (tree : WeightedGuideTree) → WeightedResourceFamily tree.trueSize
  | .leaf family _ _ => family
  | .fork _ _ left right => left.trueFamily.product right.trueFamily

def guide : (tree : WeightedGuideTree) → WeightedResourceFamily tree.guideSize
  | .leaf _ guide _ => guide
  | .fork guide _ _ _ => guide

def factor : WeightedGuideTree → ℝ
  | .leaf _ _ gamma => gamma
  | .fork _ gamma left right => left.factor * right.factor * gamma

def factors : WeightedGuideTree → List ℝ
  | .leaf _ _ gamma => [gamma]
  | .fork _ gamma left right => left.factors ++ right.factors ++ [gamma]

def LowerCertified : WeightedGuideTree → Prop
  | .leaf family guide gamma =>
      1 ≤ gamma ∧ ∀ t, guide.prefixMass t ≤ family.prefixMass t ∧
        family.prefixMass t ≤ gamma * guide.prefixMass t
  | .fork guide gamma left right =>
      1 ≤ gamma ∧ left.LowerCertified ∧ right.LowerCertified ∧
        ∀ t, guide.prefixMass t ≤ left.guide.convolution right.guide t ∧
          left.guide.convolution right.guide t ≤ gamma * guide.prefixMass t

theorem leaf_lower_certified {n p : ℕ} (family : WeightedResourceFamily n)
    (guide : WeightedResourceFamily p) (gamma : ℝ) (hg : 1 ≤ gamma)
    (hl : ∀ t, guide.prefixMass t ≤ family.prefixMass t)
    (hu : ∀ t, family.prefixMass t ≤ gamma * guide.prefixMass t) :
    (leaf family guide gamma).LowerCertified :=
  ⟨hg, fun t => ⟨hl t, hu t⟩⟩

theorem fork_lower_certified {p : ℕ} (guide : WeightedResourceFamily p)
    (gamma : ℝ) (left right : WeightedGuideTree) (hg : 1 ≤ gamma)
    (hl : left.LowerCertified) (hr : right.LowerCertified)
    (hlo : ∀ t, guide.prefixMass t ≤ left.guide.convolution right.guide t)
    (hup : ∀ t, left.guide.convolution right.guide t ≤ gamma * guide.prefixMass t) :
    (fork guide gamma left right).LowerCertified :=
  ⟨hg, hl, hr, fun t => ⟨hlo t, hup t⟩⟩

theorem factor_eq_product (tree : WeightedGuideTree) : tree.factor = tree.factors.prod := by
  induction tree with
  | leaf family guide gamma => simp [factor, factors]
  | fork guide gamma left right ihLeft ihRight =>
    simp [factor, factors, List.prod_append, ihLeft, ihRight, mul_assoc]

theorem factors_ge_one (tree : WeightedGuideTree) (h : tree.LowerCertified) :
    ∀ gamma ∈ tree.factors, 1 ≤ gamma := by
  induction tree with
  | leaf family guide gamma =>
    intro g hg
    have he : g = gamma := by simpa only [factors, List.mem_singleton] using hg
    simpa only [he] using h.1
  | fork guide gamma left right ihLeft ihRight =>
    intro g hg
    simp only [factors, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hl | hr) | he
    · exact ihLeft h.2.1 g hl
    · exact ihRight h.2.2.1 g hr
    · simpa only [he] using h.1

theorem factor_ge_one (tree : WeightedGuideTree) (h : tree.LowerCertified) :
    1 ≤ tree.factor := by
  induction tree with
  | leaf family guide gamma => exact h.1
  | fork guide gamma left right ihLeft ihRight =>
    have hl := ihLeft h.2.1
    have hr := ihRight h.2.2.1
    have hgamma := h.1
    dsimp only [factor]
    have hl0 : 0 ≤ left.factor := le_trans (by norm_num) hl
    have hr0 : 0 ≤ right.factor := le_trans (by norm_num) hr
    have hgamma0 : 0 ≤ gamma := le_trans (by norm_num) hgamma
    have hlr : 1 ≤ left.factor * right.factor := by nlinarith
    have hlr0 : 0 ≤ left.factor * right.factor := mul_nonneg hl0 hr0
    nlinarith

theorem factor_nonnegative (tree : WeightedGuideTree) (h : tree.LowerCertified) :
    0 ≤ tree.factor := le_trans (by norm_num) (factor_ge_one tree h)

theorem lower_envelope (tree : WeightedGuideTree) (h : tree.LowerCertified) (t : ℝ) :
    tree.guide.prefixMass t ≤ tree.trueFamily.prefixMass t ∧
      tree.trueFamily.prefixMass t ≤ tree.factor * tree.guide.prefixMass t := by
  induction tree generalizing t with
  | leaf family guide gamma => exact h.2 t
  | fork guide gamma left right ihLeft ihRight =>
    have hleftLower : left.guide.PrefixLE left.trueFamily := fun s => (ihLeft h.2.1 s).1
    have hrightLower : right.guide.PrefixLE right.trueFamily := fun s => (ihRight h.2.2.1 s).1
    have hleftUpper : ∀ s, left.trueFamily.prefixMass s ≤ left.factor * left.guide.prefixMass s :=
      fun s => (ihLeft h.2.1 s).2
    have hrightUpper : ∀ s, right.trueFamily.prefixMass s ≤ right.factor * right.guide.prefixMass s :=
      fun s => (ihRight h.2.2.1 s).2
    have he := WeightedResourceFamily.local_lower_guide_envelope
      guide left.guide right.guide left.trueFamily right.trueFamily
      left.factor right.factor gamma (factor_nonnegative left h.2.1)
      (factor_nonnegative right h.2.2.1) hleftLower hrightLower hleftUpper hrightUpper
      (fun s => (h.2.2.2 s).1) (fun s => (h.2.2.2 s).2) t
    change guide.prefixMass t ≤ (left.trueFamily.product right.trueFamily).prefixMass t ∧
      (left.trueFamily.product right.trueFamily).prefixMass t ≤
        (left.factor * right.factor * gamma) * guide.prefixMass t
    rw [WeightedResourceFamily.product_prefix]
    exact he

theorem prefix_zero_iff (tree : WeightedGuideTree) (h : tree.LowerCertified) (t : ℝ) :
    tree.guide.prefixMass t = 0 ↔ tree.trueFamily.prefixMass t = 0 := by
  exact WeightedResourceFamily.prefix_zero_iff_of_envelope tree.factor
    (fun s => (lower_envelope tree h s).1) (fun s => (lower_envelope tree h s).2) t

theorem prefix_positive_iff (tree : WeightedGuideTree) (h : tree.LowerCertified) (t : ℝ) :
    0 < tree.guide.prefixMass t ↔ 0 < tree.trueFamily.prefixMass t := by
  exact WeightedResourceFamily.prefix_positive_iff_of_envelope tree.factor
    (fun s => (lower_envelope tree h s).1) (fun s => (lower_envelope tree h s).2) t

theorem guide_positive_iff_feasible_label (tree : WeightedGuideTree)
    (h : tree.LowerCertified) (t : ℝ) :
    0 < tree.guide.prefixMass t ↔
      ∃ i, tree.trueFamily.resource i ≤ t ∧ 0 < tree.trueFamily.mass i :=
  (prefix_positive_iff tree h t).trans (tree.trueFamily.prefix_positive_iff_exists t)

/- At a non-leaf drawing root the guide itself is unnecessary: the child
synthetic convolution has the same zero set and a child-product envelope. -/
theorem root_synthetic_envelope (left right : WeightedGuideTree)
    (hl : left.LowerCertified) (hr : right.LowerCertified) (t : ℝ) :
    left.guide.convolution right.guide t ≤ left.trueFamily.convolution right.trueFamily t ∧
      left.trueFamily.convolution right.trueFamily t ≤
        (left.factor * right.factor) * left.guide.convolution right.guide t := by
  constructor
  · exact WeightedResourceFamily.convolution_mono
      (fun s => (lower_envelope left hl s).1) (fun s => (lower_envelope right hr s).1) t
  · exact WeightedResourceFamily.convolution_upper_envelope left.factor right.factor
      (factor_nonnegative left hl) (factor_nonnegative right hr)
      (fun s => (lower_envelope left hl s).2) (fun s => (lower_envelope right hr s).2) t

theorem root_synthetic_positive_iff (left right : WeightedGuideTree)
    (hl : left.LowerCertified) (hr : right.LowerCertified) (t : ℝ) :
    0 < left.guide.convolution right.guide t ↔
      0 < left.trueFamily.convolution right.trueFamily t := by
  have he := WeightedResourceFamily.prefix_positive_iff_of_envelope
    (left.factor * right.factor)
    (a := left.guide.product right.guide) (b := left.trueFamily.product right.trueFamily)
    (fun s => by
      rw [WeightedResourceFamily.product_prefix, WeightedResourceFamily.product_prefix]
      exact (root_synthetic_envelope left right hl hr s).1)
    (fun s => by
      rw [WeightedResourceFamily.product_prefix, WeightedResourceFamily.product_prefix]
      exact (root_synthetic_envelope left right hl hr s).2) t
  simpa only [WeightedResourceFamily.product_prefix] using he

end WeightedGuideTree
end Blotto
