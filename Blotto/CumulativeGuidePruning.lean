import Blotto.WeightedPrefixConvolution

/-! Deterministic lower-guide pruning of complete rational resource groups.
The input must already be grouped and strictly ordered. Aggregating raw ties
is a separate obligation. The scan uses exact cumulative heights, not bins
of true subtree states. -/

namespace Blotto
open scoped Classical

namespace CumulativeGuidePruning

abbrev Atom := ℚ × ℚ

def scan (gamma : ℚ) : List Atom → ℚ → ℚ → List Atom
  | [], _, _ => []
  | atom :: rest, cumulative, retained =>
      let next := cumulative + atom.2
      if gamma * retained < next then
        (atom.1, next - retained) :: scan gamma rest next next
      else scan gamma rest next retained

def prune (gamma : ℚ) (groups : List Atom) : List Atom := scan gamma groups 0 0

noncomputable def prefixMass : List Atom → ℝ → ℚ
  | [], _ => 0
  | atom :: rest, t => (if (atom.1 : ℝ) ≤ t then atom.2 else 0) + prefixMass rest t

def Nonnegative (groups : List Atom) : Prop := ∀ atom ∈ groups, 0 ≤ atom.2

def StrictlyGrouped (groups : List Atom) : Prop :=
  groups.Pairwise (fun a b => a.1 < b.1)

theorem prefixMass_nonnegative (groups : List Atom) (h : Nonnegative groups) (t : ℝ) :
    0 ≤ prefixMass groups t := by
  induction groups with
  | nil => exact le_rfl
  | cons atom rest ih =>
    have hh := h atom (by simp)
    have ht : Nonnegative rest := fun a ha => h a (by simp [ha])
    change 0 ≤ (if (atom.1 : ℝ) ≤ t then atom.2 else 0) + prefixMass rest t
    split_ifs
    · exact add_nonneg hh (ih ht)
    · exact add_nonneg le_rfl (ih ht)

theorem scan_nonnegative (groups : List Atom) (gamma cumulative retained : ℚ)
    (hgroups : Nonnegative groups)
    (hc : 0 ≤ cumulative) (hh : 0 ≤ retained) (horder : retained ≤ cumulative) :
    Nonnegative (scan gamma groups cumulative retained) := by
  induction groups generalizing cumulative retained with
  | nil => intro a ha; simp [scan] at ha
  | cons atom rest ih =>
    have ha := hgroups atom (by simp)
    have ht : Nonnegative rest := fun a ha => hgroups a (by simp [ha])
    have hn : 0 ≤ cumulative + atom.2 := add_nonneg hc ha
    have hr : retained ≤ cumulative + atom.2 := le_trans horder (le_add_of_nonneg_right ha)
    dsimp only [scan]
    split_ifs
    · intro a ha
      rcases List.mem_cons.mp ha with he | he
      · rw [he]
        exact sub_nonneg.mpr hr
      · exact ih (cumulative + atom.2) (cumulative + atom.2) ht hn hn le_rfl a he
    · exact ih (cumulative + atom.2) retained ht hn hh hr

theorem prune_nonnegative (groups : List Atom) (gamma : ℚ)
    (hgroups : Nonnegative groups) : Nonnegative (prune gamma groups) :=
  scan_nonnegative groups gamma 0 0 hgroups le_rfl le_rfl le_rfl

theorem scan_resources_sublist (groups : List Atom) (gamma cumulative retained : ℚ) :
    List.Sublist ((scan gamma groups cumulative retained).map Prod.fst) (groups.map Prod.fst) := by
  induction groups generalizing cumulative retained with
  | nil => exact List.Sublist.refl _
  | cons atom rest ih =>
    dsimp only [scan]
    split_ifs
    · exact (ih _ _).cons_cons atom.1
    · exact (ih _ _).cons atom.1

theorem scan_strictly_grouped (groups : List Atom) (gamma cumulative retained : ℚ)
    (h : StrictlyGrouped groups) : StrictlyGrouped (scan gamma groups cumulative retained) := by
  have hmap : (groups.map Prod.fst).Pairwise (· < ·) := by
    simpa only [StrictlyGrouped, List.pairwise_map] using h
  have he := hmap.sublist (scan_resources_sublist groups gamma cumulative retained)
  simpa only [StrictlyGrouped, List.pairwise_map] using he

theorem prune_strictly_grouped (groups : List Atom) (gamma : ℚ)
    (h : StrictlyGrouped groups) : StrictlyGrouped (prune gamma groups) :=
  scan_strictly_grouped groups gamma 0 0 h

theorem prune_length_le (groups : List Atom) (gamma : ℚ) :
    (prune gamma groups).length ≤ groups.length := by
  have he := (scan_resources_sublist groups gamma 0 0).length_le
  simpa only [List.length_map, prune] using he

theorem prefixMass_zero_of_after (groups : List Atom) (t : ℝ)
    (h : ∀ atom ∈ groups, t < (atom.1 : ℝ)) : prefixMass groups t = 0 := by
  induction groups with
  | nil => rfl
  | cons atom rest ih =>
    have ha := h atom (by simp)
    have ht : ∀ a ∈ rest, t < (a.1 : ℝ) := fun a ha => h a (by simp [ha])
    simp only [prefixMass, not_le_of_gt ha, ite_false, zero_add, ih ht]

theorem scan_prefixMass_zero_of_after (groups : List Atom) (gamma cumulative retained : ℚ) (t : ℝ)
    (h : ∀ atom ∈ groups, t < (atom.1 : ℝ)) :
    prefixMass (scan gamma groups cumulative retained) t = 0 := by
  apply prefixMass_zero_of_after
  intro atom ha
  have hm : atom.1 ∈ groups.map Prod.fst :=
    (scan_resources_sublist groups gamma cumulative retained).subset (List.mem_map.mpr ⟨atom, ha, rfl⟩)
  rcases List.mem_map.mp hm with ⟨source, hs, he⟩
  rw [← he]
  exact h source hs

/- `cumulative` and `retained` include the already processed prefix. The
remaining groups begin strictly later. This invariant controls arbitrary
real cutoffs, including exact resource equality and every open gap. -/
theorem scan_prefix_envelope (groups : List Atom) (gamma cumulative retained : ℚ)
    (hgamma : 1 ≤ gamma) (hgroups : Nonnegative groups) (hsorted : StrictlyGrouped groups)
    (hc : 0 ≤ cumulative) (hh : 0 ≤ retained)
    (hl : retained ≤ cumulative) (hu : cumulative ≤ gamma * retained) (t : ℝ) :
    retained + prefixMass (scan gamma groups cumulative retained) t ≤
        cumulative + prefixMass groups t ∧
      cumulative + prefixMass groups t ≤
        gamma * (retained + prefixMass (scan gamma groups cumulative retained) t) := by
  induction groups generalizing cumulative retained with
  | nil => simpa only [scan, prefixMass, add_zero] using And.intro hl hu
  | cons atom rest ih =>
    have ha := hgroups atom (by simp)
    have ht : Nonnegative rest := fun a ha => hgroups a (by simp [ha])
    have hrest : StrictlyGrouped rest := (List.pairwise_cons.mp hsorted).2
    have hafter : ∀ a ∈ rest, atom.1 < a.1 := (List.pairwise_cons.mp hsorted).1
    have hn : 0 ≤ cumulative + atom.2 := add_nonneg hc ha
    have hr : retained ≤ cumulative + atom.2 := le_trans hl (le_add_of_nonneg_right ha)
    by_cases hcut : (atom.1 : ℝ) ≤ t
    · by_cases hkeep : gamma * retained < cumulative + atom.2
      · have hnUpper : cumulative + atom.2 ≤ gamma * (cumulative + atom.2) := by
          nlinarith
        have he := ih (cumulative + atom.2) (cumulative + atom.2) ht hrest hn hn le_rfl hnUpper
        simp only [scan, hkeep, ite_true, prefixMass, hcut] at *
        constructor <;> linarith [he.1, he.2]
      · have he := ih (cumulative + atom.2) retained ht hrest hn hh hr (le_of_not_gt hkeep)
        simp only [scan, hkeep, ite_false, prefixMass, hcut, ite_true]
        constructor <;> linarith [he.1, he.2]
    · have hless : t < (atom.1 : ℝ) := lt_of_not_ge hcut
      have htail : ∀ a ∈ rest, t < (a.1 : ℝ) := by
        intro a ha
        have he : (atom.1 : ℝ) < (a.1 : ℝ) := by exact_mod_cast hafter a ha
        exact hless.trans he
      have htailZero := prefixMass_zero_of_after rest t htail
      have hscanZero : prefixMass (scan gamma (atom :: rest) cumulative retained) t = 0 := by
        apply scan_prefixMass_zero_of_after
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hless
        · exact htail a ha
      simp only [hscanZero, prefixMass, hcut, ite_false, htailZero, add_zero]
      exact ⟨hl, hu⟩

theorem prune_envelope (groups : List Atom) (gamma : ℚ) (hgamma : 1 ≤ gamma)
    (hgroups : Nonnegative groups) (hsorted : StrictlyGrouped groups) (t : ℝ) :
    prefixMass (prune gamma groups) t ≤ prefixMass groups t ∧
      prefixMass groups t ≤ gamma * prefixMass (prune gamma groups) t := by
  simpa only [prune, zero_add] using
    scan_prefix_envelope groups gamma 0 0 hgamma hgroups hsorted le_rfl le_rfl le_rfl
      (by simp) t

theorem prune_zero_iff (groups : List Atom) (gamma : ℚ) (hgamma : 1 ≤ gamma)
    (hgroups : Nonnegative groups) (hsorted : StrictlyGrouped groups) (t : ℝ) :
    prefixMass (prune gamma groups) t = 0 ↔ prefixMass groups t = 0 := by
  have he := prune_envelope groups gamma hgamma hgroups hsorted t
  constructor
  · intro hz
    rw [hz, mul_zero] at he
    exact le_antisymm he.2 (prefixMass_nonnegative groups hgroups t)
  · intro hz
    rw [hz] at he
    exact le_antisymm he.1 (prefixMass_nonnegative _ (prune_nonnegative groups gamma hgroups) t)

theorem prune_positive_iff (groups : List Atom) (gamma : ℚ) (hgamma : 1 ≤ gamma)
    (hgroups : Nonnegative groups) (hsorted : StrictlyGrouped groups) (t : ℝ) :
    0 < prefixMass (prune gamma groups) t ↔ 0 < prefixMass groups t := by
  have he := prune_envelope groups gamma hgamma hgroups hsorted t
  have hz := prune_zero_iff groups gamma hgamma hgroups hsorted t
  constructor
  · intro hp
    exact hp.trans_le he.1
  · intro hp
    have hn : prefixMass (prune gamma groups) t ≠ 0 := fun hn => (ne_of_gt hp) (hz.mp hn)
    exact lt_of_le_of_ne (prefixMass_nonnegative _ (prune_nonnegative groups gamma hgroups) t)
      (Ne.symm hn)

theorem prune_real_envelope (groups : List Atom) (gamma : ℚ) (hgamma : 1 ≤ gamma)
    (hgroups : Nonnegative groups) (hsorted : StrictlyGrouped groups) (t : ℝ) :
    (prefixMass (prune gamma groups) t : ℝ) ≤ (prefixMass groups t : ℝ) ∧
      (prefixMass groups t : ℝ) ≤ (gamma : ℝ) * (prefixMass (prune gamma groups) t : ℝ) := by
  have he := prune_envelope groups gamma hgamma hgroups hsorted t
  constructor
  · exact_mod_cast he.1
  · exact_mod_cast he.2

end CumulativeGuidePruning
end Blotto
