import Blotto.PlayerSpecificIsolationState

/-! Actual depth-bounded rational bisection, pruning exactly the zero-count
branches. Depth is still an explicit control parameter here; deriving it
from computed coefficient/separation bounds remains necessary. -/
namespace Blotto.PlayerSpecificIsolationForest
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState
set_option autoImplicit false
set_option maxHeartbeats 4000000

def run {p : Data} (prepared : Prepared p) : ℕ → Interval → List Interval
  | 0,node => if node.count=0 then [] else [node]
  | fuel+1,node => if node.count=0 then [] else
      let parts := split prepared node
      run prepared fuel parts.1++run prepared fuel parts.2

theorem valid_positive {p : Data} (prepared : Prepared p) (fuel : ℕ) (node : Interval) (h : Valid prepared node) :
    ∀ leaf∈run prepared fuel node,Valid prepared leaf ∧ 0<leaf.count := by
  induction fuel generalizing node with
  | zero =>
    rw [run]
    split
    · intro leaf hleaf
      simp only [List.not_mem_nil] at hleaf
    · rename_i hn
      intro leaf hleaf
      have he := List.mem_singleton.mp hleaf
      subst leaf
      exact ⟨h,Nat.pos_of_ne_zero hn⟩
  | succ fuel ih =>
    rw [run]
    split
    · intro leaf hleaf
      simp only [List.not_mem_nil] at hleaf
    · have hv := split_valid prepared node h
      intro leaf hleaf
      rcases List.mem_append.mp hleaf with hl | hr
      · exact ih (split prepared node).1 hv.1 leaf hl
      · exact ih (split prepared node).2 hv.2 leaf hr

theorem count_mass {p : Data} (prepared : Prepared p) (hp : semantics p≠0) (fuel : ℕ)
    (node : Interval) (h : Valid prepared node) :
    ((run prepared fuel node).map Interval.count).sum=node.count := by
  induction fuel generalizing node with
  | zero =>
    rw [run]
    split
    · rename_i hz
      simp only [List.map_nil,List.sum_nil,hz]
    · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  | succ fuel ih =>
    rw [run]
    split
    · rename_i hz
      simp only [List.map_nil,List.sum_nil,hz]
    · have hv := split_valid prepared node h
      rw [List.map_append,List.sum_append,ih (split prepared node).1 hv.1,ih (split prepared node).2 hv.2]
      exact (split_counts prepared hp node h).symm

theorem length_le_mass (xs : List Interval) (h : ∀ node∈xs,0<node.count) :
    xs.length≤(xs.map Interval.count).sum := by
  induction xs with
  | nil => exact le_rfl
  | cons node xs ih =>
    have hh := h node (by simp only [List.mem_cons_self])
    have ht := ih (fun leaf hleaf => h leaf (List.mem_cons_of_mem _ hleaf))
    simp only [List.length_cons,List.map_cons,List.sum_cons]
    omega

theorem length_bound {p : Data} (prepared : Prepared p) (hp : semantics p≠0) (fuel : ℕ)
    (node : Interval) (h : Valid prepared node) : (run prepared fuel node).length≤node.count := by
  have hm := length_le_mass (run prepared fuel node) (fun leaf hleaf => (valid_positive prepared fuel node h leaf hleaf).2)
  rw [count_mass prepared hp fuel node h] at hm
  exact hm

theorem contained {p : Data} (prepared : Prepared p) (fuel : ℕ) (node : Interval) (h : Valid prepared node) :
    ∀ leaf∈run prepared fuel node,∀ x,leaf.Contains x → node.Contains x := by
  induction fuel generalizing node with
  | zero =>
    rw [run]
    split
    · intro leaf hleaf
      simp only [List.not_mem_nil] at hleaf
    · intro leaf hleaf x hx
      have he := List.mem_singleton.mp hleaf
      subst leaf
      exact hx
  | succ fuel ih =>
    rw [run]
    split
    · intro leaf hleaf
      simp only [List.not_mem_nil] at hleaf
    · have hv := split_valid prepared node h
      intro leaf hleaf x hx
      apply (split_cover prepared node h.1 x).mpr
      rcases List.mem_append.mp hleaf with hl | hr
      · exact Or.inl (ih (split prepared node).1 hv.1 leaf hl x hx)
      · exact Or.inr (ih (split prepared node).2 hv.2 leaf hr x hx)

theorem coverage {p : Data} (prepared : Prepared p) (hp : semantics p≠0) (fuel : ℕ)
    (node : Interval) (h : Valid prepared node) (x : ℝ) (hx : PlayerSpecificSturmVariations.realEvaluate p x=0) :
    node.Contains x ↔ ∃ leaf∈run prepared fuel node,leaf.Contains x := by
  induction fuel generalizing node with
  | zero =>
    rw [run]
    split
    · rename_i hz
      constructor
      · intro hc
        have hcpos := (positive_iff prepared hp node h).mpr ⟨x,hx,hc⟩
        omega
      · rintro ⟨leaf,hleaf,_⟩
        simp only [List.not_mem_nil] at hleaf
    · constructor
      · intro hc
        exact ⟨node,List.mem_singleton_self _,hc⟩
      · rintro ⟨leaf,hleaf,hc⟩
        have he := List.mem_singleton.mp hleaf
        subst leaf
        exact hc
  | succ fuel ih =>
    rw [run]
    split
    · rename_i hz
      constructor
      · intro hc
        have hcpos := (positive_iff prepared hp node h).mpr ⟨x,hx,hc⟩
        omega
      · rintro ⟨leaf,hleaf,_⟩
        simp only [List.not_mem_nil] at hleaf
    · have hv := split_valid prepared node h
      constructor
      · intro hc
        rcases (split_cover prepared node h.1 x).mp hc with hl | hr
        · rcases (ih (split prepared node).1 hv.1).mp hl with ⟨leaf,hleaf,hcontains⟩
          exact ⟨leaf,List.mem_append_left _ hleaf,hcontains⟩
        · rcases (ih (split prepared node).2 hv.2).mp hr with ⟨leaf,hleaf,hcontains⟩
          exact ⟨leaf,List.mem_append_right _ hleaf,hcontains⟩
      · rintro ⟨leaf,hleaf,hcontains⟩
        apply (split_cover prepared node h.1 x).mpr
        rcases List.mem_append.mp hleaf with hl | hr
        · exact Or.inl ((ih (split prepared node).1 hv.1).mpr ⟨leaf,hl,hcontains⟩)
        · exact Or.inr ((ih (split prepared node).2 hv.2).mpr ⟨leaf,hr,hcontains⟩)

/-- The number of recursive source calls, including pruned empty children. -/
def visits {p : Data} (prepared : Prepared p) : ℕ → Interval → ℕ
  | 0,_ => 1
  | fuel+1,node => if node.count=0 then 1 else
      let parts := split prepared node
      1+visits prepared fuel parts.1+visits prepared fuel parts.2

theorem visits_bound {p : Data} (prepared : Prepared p) (hp : semantics p≠0) (fuel : ℕ)
    (node : Interval) (h : Valid prepared node) : visits prepared fuel node≤2*fuel*node.count+1 := by
  induction fuel generalizing node with
  | zero => simp only [visits,Nat.mul_zero,Nat.zero_mul,Nat.zero_add]; exact le_rfl
  | succ fuel ih =>
    rw [visits]
    split
    · omega
    · rename_i hn
      have hv := split_valid prepared node h
      have hl := ih (split prepared node).1 hv.1
      have hr := ih (split prepared node).2 hv.2
      have hc := split_counts prepared hp node h
      have hSum := Nat.add_le_add hl hr
      nlinarith only [hSum,hc,Nat.pos_of_ne_zero hn]

end Blotto.PlayerSpecificIsolationForest
