import Blotto.PlayerSpecificIsolationForest

/-! Exact dyadic widths and geometric non-overlap of the actually retained
leaves. These hold at every depth; a computed separation-based depth for
complete root isolation remains a later caller. -/
namespace Blotto.PlayerSpecificIsolationGeometry
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificIsolationForest
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem half_div_power (x : ℚ) (depth : ℕ) : (x/2)/(2:ℚ)^depth=x/(2:ℚ)^(depth+1) := by
  rw [div_div,pow_succ,mul_comm (2 : ℚ)]

theorem width {p : Data} (prepared : Prepared p) (fuel : ℕ) (node : Interval) :
    ∀ leaf∈run prepared fuel node,leaf.width=node.width/(2:ℚ)^fuel := by
  induction fuel generalizing node with
  | zero =>
    rw [run]
    split
    · intro leaf hleaf
      simp only [List.not_mem_nil] at hleaf
    · intro leaf hleaf
      have he := List.mem_singleton.mp hleaf
      subst leaf
      simp only [pow_zero,div_one]
  | succ fuel ih =>
    rw [run]
    split
    · intro leaf hleaf
      simp only [List.not_mem_nil] at hleaf
    · have hw := split_width prepared node
      intro leaf hleaf
      rcases List.mem_append.mp hleaf with hl | hr
      · rw [ih (split prepared node).1 leaf hl,hw.1,half_div_power]
      · rw [ih (split prepared node).2 leaf hr,hw.2,half_div_power]

theorem member_le_mass (xs : List Interval) (leaf : Interval) (h : leaf∈xs) :
    leaf.count≤(xs.map Interval.count).sum := by
  induction xs with
  | nil => simp only [List.not_mem_nil] at h
  | cons node xs ih =>
    simp only [List.map_cons,List.sum_cons]
    rcases List.mem_cons.mp h with he | ht
    · subst leaf
      omega
    · have hh := ih ht
      omega

theorem count_bound {p : Data} (prepared : Prepared p) (hp : semantics p≠0) (fuel : ℕ)
    (node : Interval) (h : Valid prepared node) (leaf : Interval) (hleaf : leaf∈run prepared fuel node) :
    leaf.count≤node.count := by
  have hm := member_le_mass (run prepared fuel node) leaf hleaf
  rw [count_mass prepared hp fuel node h] at hm
  exact hm

theorem same_at_point {p : Data} (prepared : Prepared p) (fuel : ℕ) (node : Interval) (h : Valid prepared node) :
    ∀ a∈run prepared fuel node,∀ b∈run prepared fuel node,∀ x,a.Contains x → b.Contains x → a=b := by
  induction fuel generalizing node with
  | zero =>
    rw [run]
    split
    · intro a ha
      simp only [List.not_mem_nil] at ha
    · intro a ha b hb _ _ _
      exact (List.mem_singleton.mp ha).trans (List.mem_singleton.mp hb).symm
  | succ fuel ih =>
    rw [run]
    split
    · intro a ha
      simp only [List.not_mem_nil] at ha
    · have hv := split_valid prepared node h
      intro a ha b hb x hax hbx
      rcases List.mem_append.mp ha with hal | har <;> rcases List.mem_append.mp hb with hbl | hbr
      · exact ih (split prepared node).1 hv.1 a hal b hbl x hax hbx
      · exact False.elim (split_disjoint prepared node x
          ⟨contained prepared fuel (split prepared node).1 hv.1 a hal x hax,
            contained prepared fuel (split prepared node).2 hv.2 b hbr x hbx⟩)
      · exact False.elim (split_disjoint prepared node x
          ⟨contained prepared fuel (split prepared node).1 hv.1 b hbl x hbx,
            contained prepared fuel (split prepared node).2 hv.2 a har x hax⟩)
      · exact ih (split prepared node).2 hv.2 a har b hbr x hax hbx

theorem unique_root {p : Data} (prepared : Prepared p) (hp : semantics p≠0) (fuel : ℕ)
    (node : Interval) (h : Valid prepared node) (leaf : Interval) (hleaf : leaf∈run prepared fuel node)
    (hcount : leaf.count=1) : ∃! x : ℝ,PlayerSpecificSturmVariations.realEvaluate p x=0 ∧ leaf.Contains x := by
  have hv := (valid_positive prepared fuel node h leaf hleaf).1
  apply PlayerSpecificSturmRootCount.one_unique p hp leaf.lo leaf.hi hv.1.le
  rw [← count_eq prepared leaf hv]
  exact hcount

end Blotto.PlayerSpecificIsolationGeometry
