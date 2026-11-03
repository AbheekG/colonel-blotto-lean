import Blotto.WeightedGuideFactorBound

/-! Uniform per-node guide tolerances budget the actual factor product. These
bounds charge every stored node, including the root; constructing guides with
those tolerances is separate from proving the resulting budget. -/

namespace Blotto
open scoped BigOperators
namespace WeightedGuideTree

def nodeCount (tree : WeightedGuideTree) : ℕ := tree.factors.length

theorem nodeCount_positive (tree : WeightedGuideTree) : 0 < tree.nodeCount := by
  induction tree with
  | leaf family guide gamma => exact Nat.zero_lt_one
  | fork guide gamma left right ihL ihR => simp [nodeCount, factors]

theorem uniform_local_error_budget (tree : WeightedGuideTree)
    (hGamma : ∀ gamma ∈ tree.factors, gamma ≤ 1 + 1 / (8 * (tree.nodeCount : ℝ))) :
    tree.localErrorSum ≤ 1 / 8 := by
  have hCount : (0 : ℝ) < tree.nodeCount := by exact_mod_cast tree.nodeCount_positive
  have hEach : ∀ delta ∈ tree.factors.map (fun gamma => gamma - 1),
      delta ≤ 1 / (8 * (tree.nodeCount : ℝ)) := by
    intro delta hdelta
    rcases List.mem_map.mp hdelta with ⟨gamma, hg, rfl⟩
    linarith [hGamma gamma hg]
  have hSum : (tree.factors.map (fun gamma => gamma - 1)).sum ≤
      (tree.factors.length : ℝ) * (1 / (8 * (tree.nodeCount : ℝ))) := by
    have hs : ∀ xs : List ℝ, (∀ x ∈ xs, x ≤ 1 / (8 * (tree.nodeCount : ℝ))) →
        xs.sum ≤ (xs.length : ℝ) * (1 / (8 * (tree.nodeCount : ℝ))) := by
      intro xs
      induction xs with
      | nil => intros; simp
      | cons x rest ih =>
        intro h
        have hh := h x (by simp)
        have ht := ih (fun y hy => h y (by simp [hy]))
        simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        nlinarith
    simpa only [List.length_map] using hs _ hEach
  change tree.localErrorSum ≤ _
  unfold localErrorSum
  have he : (tree.factors.length : ℝ) * (1 / (8 * (tree.nodeCount : ℝ))) = 1 / 8 := by
    change (tree.nodeCount : ℝ) * (1 / (8 * (tree.nodeCount : ℝ))) = 1 / 8
    field_simp
  exact hSum.trans_eq he

theorem uniform_factor_bound (tree : WeightedGuideTree) (hc : tree.LowerCertified)
    (hGamma : ∀ gamma ∈ tree.factors, gamma ≤ 1 + 1 / (8 * (tree.nodeCount : ℝ))) : tree.factor ≤ 8 / 7 :=
  tree.factor_le_eight_sevenths hc (tree.uniform_local_error_budget hGamma)

end WeightedGuideTree
end Blotto
