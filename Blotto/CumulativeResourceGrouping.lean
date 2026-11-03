import Blotto.CumulativeGuidePruning

/-! Adjacent equal-resource groups are summed before cumulative pruning.
The caller supplies a nondecreasing rational resource list; sorting itself
is not claimed here. Labels with equal resources contribute their full mass. -/

namespace Blotto
open scoped Classical

namespace CumulativeResourceGrouping
open CumulativeGuidePruning

def collect : List Atom → Atom → List Atom
  | [], current => [current]
  | atom :: rest, current =>
      if atom.1 = current.1 then
        collect rest (current.1, current.2 + atom.2)
      else current :: collect rest atom

def group : List Atom → List Atom
  | [] => []
  | atom :: rest => collect rest atom

def Nondecreasing (atoms : List Atom) : Prop :=
  atoms.Pairwise (fun a b => a.1 ≤ b.1)

theorem collect_nonnegative (atoms : List Atom) (current : Atom)
    (h : Nonnegative atoms) (hc : 0 ≤ current.2) : Nonnegative (collect atoms current) := by
  induction atoms generalizing current with
  | nil =>
    intro a ha
    have he : a = current := by simpa only [collect, List.mem_singleton] using ha
    simpa only [he] using hc
  | cons atom rest ih =>
    have ha := h atom (by simp)
    have ht : Nonnegative rest := fun a ha => h a (by simp [ha])
    dsimp only [collect]
    split_ifs
    · exact ih _ ht (add_nonneg hc ha)
    · intro a haMem
      rcases List.mem_cons.mp haMem with rfl | haMem
      · exact hc
      · exact ih atom ht ha a haMem

theorem group_nonnegative (atoms : List Atom) (h : Nonnegative atoms) : Nonnegative (group atoms) := by
  cases atoms with
  | nil => intro a ha; simp [group] at ha
  | cons atom rest =>
    exact collect_nonnegative rest atom (fun a ha => h a (by simp [ha])) (h atom (by simp))

theorem collect_length_le (atoms : List Atom) (current : Atom) :
    (collect atoms current).length ≤ atoms.length + 1 := by
  induction atoms generalizing current with
  | nil => simp [collect]
  | cons atom rest ih =>
    dsimp only [collect]
    split_ifs
    · have he := ih (current.1, current.2 + atom.2)
      simp only [List.length_cons]
      omega
    · have he := ih atom
      simp only [List.length_cons]
      omega

theorem group_length_le (atoms : List Atom) : (group atoms).length ≤ atoms.length := by
  cases atoms with
  | nil => exact le_rfl
  | cons atom rest => exact collect_length_le rest atom

theorem collect_prefixMass (atoms : List Atom) (current : Atom) (t : ℝ) :
    prefixMass (collect atoms current) t =
      (if (current.1 : ℝ) ≤ t then current.2 else 0) + prefixMass atoms t := by
  induction atoms generalizing current with
  | nil => simp [collect, prefixMass]
  | cons atom rest ih =>
    dsimp only [collect]
    by_cases he : atom.1 = current.1
    · rw [ite_eq_left he, ih]
      dsimp only [Prod.fst, Prod.snd]
      simp only [prefixMass, he]
      split_ifs <;> ring
    · rw [ite_eq_right he, prefixMass, ih, prefixMass]

theorem group_prefixMass (atoms : List Atom) (t : ℝ) :
    prefixMass (group atoms) t = prefixMass atoms t := by
  cases atoms with
  | nil => rfl
  | cons atom rest => exact collect_prefixMass rest atom t

theorem collect_resource_origin (atoms : List Atom) (current : Atom)
    (out : Atom) (ho : out ∈ collect atoms current) :
    out.1 = current.1 ∨ ∃ atom ∈ atoms, out.1 = atom.1 := by
  induction atoms generalizing current with
  | nil =>
    have he : out = current := by simpa only [collect, List.mem_singleton] using ho
    exact Or.inl (congrArg Prod.fst he)
  | cons atom rest ih =>
    dsimp only [collect] at ho
    split_ifs at ho with he
    · rcases ih (current.1, current.2 + atom.2) ho with hcur | ⟨a, ha, he⟩
      · exact Or.inl hcur
      · exact Or.inr ⟨a, by simp [ha], he⟩
    · rcases List.mem_cons.mp ho with rfl | ho
      · exact Or.inl rfl
      · rcases ih atom ho with hcur | ⟨a, ha, he⟩
        · exact Or.inr ⟨atom, by simp, hcur⟩
        · exact Or.inr ⟨a, by simp [ha], he⟩

theorem collect_resource_lower_bound (atoms : List Atom) (current : Atom)
    (h : ∀ atom ∈ atoms, current.1 ≤ atom.1) :
    ∀ atom ∈ collect atoms current, current.1 ≤ atom.1 := by
  intro out ho
  rcases collect_resource_origin atoms current out ho with he | ⟨a, ha, he⟩
  · rw [he]
  · rw [he]
    exact h a ha

theorem collect_strictly_grouped (atoms : List Atom) (current : Atom)
    (h : Nondecreasing atoms) (hc : ∀ atom ∈ atoms, current.1 ≤ atom.1) :
    StrictlyGrouped (collect atoms current) := by
  induction atoms generalizing current with
  | nil => simp [collect, StrictlyGrouped]
  | cons atom rest ih =>
    have ht : Nondecreasing rest := (List.pairwise_cons.mp h).2
    have hhead : ∀ a ∈ rest, atom.1 ≤ a.1 := (List.pairwise_cons.mp h).1
    have hcur := hc atom (by simp)
    dsimp only [collect]
    split_ifs with he
    · exact ih (current.1, current.2 + atom.2) ht (fun a ha => hc a (by simp [ha]))
    · apply List.pairwise_cons.mpr
      constructor
      · intro a ha
        have hl := collect_resource_lower_bound rest atom hhead a ha
        have hlt : current.1 < atom.1 := lt_of_le_of_ne hcur (Ne.symm he)
        exact hlt.trans_le hl
      · exact ih atom ht hhead

theorem group_strictly_grouped (atoms : List Atom) (h : Nondecreasing atoms) :
    StrictlyGrouped (group atoms) := by
  cases atoms with
  | nil => simp [group, StrictlyGrouped]
  | cons atom rest =>
    exact collect_strictly_grouped rest atom (List.pairwise_cons.mp h).2 (List.pairwise_cons.mp h).1

theorem grouped_prune_envelope (atoms : List Atom) (gamma : ℚ) (hgamma : 1 ≤ gamma)
    (hweights : Nonnegative atoms) (hsorted : Nondecreasing atoms) (t : ℝ) :
    prefixMass (prune gamma (group atoms)) t ≤ prefixMass atoms t ∧
      prefixMass atoms t ≤ gamma * prefixMass (prune gamma (group atoms)) t := by
  have he := prune_envelope (group atoms) gamma hgamma (group_nonnegative atoms hweights)
    (group_strictly_grouped atoms hsorted) t
  rw [group_prefixMass] at he
  exact he

theorem grouped_prune_zero_iff (atoms : List Atom) (gamma : ℚ) (hgamma : 1 ≤ gamma)
    (hweights : Nonnegative atoms) (hsorted : Nondecreasing atoms) (t : ℝ) :
    prefixMass (prune gamma (group atoms)) t = 0 ↔ prefixMass atoms t = 0 := by
  have he := prune_zero_iff (group atoms) gamma hgamma (group_nonnegative atoms hweights)
    (group_strictly_grouped atoms hsorted) t
  rw [group_prefixMass] at he
  exact he

end CumulativeResourceGrouping
end Blotto
