import Blotto.AffineMixture

/-! Terminating conditional resource-rounding lotteries. The correctness and
update bound hold for any valid pair selector. A maintained-list/array
implementation and its operation counts are separate refinement obligations. -/

namespace Blotto
open MeasureTheory Set
open scoped BigOperators

structure FractionalPair {n : ℕ} (length resource : Allocation n) where
  i : Fin n
  j : Fin n
  distinct : i ≠ j
  interior_i : Fractional length resource i
  interior_j : Fractional length resource j

noncomputable def chooseFractionalPair {n : ℕ} (length resource : Allocation n)
    (h : 1 < (fractionalSet length resource).card) : FractionalPair length resource := by
  classical
  have he := Finset.one_lt_card.mp h
  let i := Classical.choose he
  have hi := Classical.choose_spec he
  let j := Classical.choose hi.2
  have hj := Classical.choose_spec hi.2
  exact ⟨i, j, hj.2, (mem_fractionalSet _ _ _).mp hi.1, (mem_fractionalSet _ _ _).mp hj.1⟩

noncomputable def roundResources {n : ℕ} (length : Allocation n)
    (select : ∀ resource : Allocation n, 1 < (fractionalSet length resource).card → FractionalPair length resource) :
    ℕ → Allocation n → RoundingTree n
  | 0, resource => .leaf resource
  | fuel + 1, resource =>
    if h : 1 < (fractionalSet length resource).card then
      let c := select resource h
      let r := resourcePair length resource c.i c.j c.interior_i c.interior_j
      .fork r.probability ⟨le_of_lt r.probability_pos, le_of_lt r.probability_lt_one⟩
        (roundResources length select fuel (updatePair resource c.i c.j r.upper))
        (roundResources length select fuel (updatePair resource c.i c.j r.lower))
    else .leaf resource

theorem roundResources_height {n : ℕ} (length : Allocation n)
    (select : ∀ resource : Allocation n, 1 < (fractionalSet length resource).card → FractionalPair length resource)
    (fuel : ℕ) (resource : Allocation n) : (roundResources length select fuel resource).height ≤ fuel := by
  induction fuel generalizing resource with
  | zero => simp [roundResources, RoundingTree.height]
  | succ fuel ih =>
    unfold roundResources
    split_ifs with h
    · change 1 + max (roundResources length select fuel _).height
        (roundResources length select fuel _).height ≤ fuel + 1
      have hA := ih (updatePair resource (select resource h).i (select resource h).j
        (resourcePair length resource _ _ (select resource h).interior_i (select resource h).interior_j).upper)
      have hB := ih (updatePair resource (select resource h).i (select resource h).j
        (resourcePair length resource _ _ (select resource h).interior_i (select resource h).interior_j).lower)
      exact Nat.add_le_add_left (max_le hA hB) 1 |>.trans (by omega)
    · simp [RoundingTree.height]

theorem roundResources_average {n : ℕ} (length : Allocation n)
    (select : ∀ resource : Allocation n, 1 < (fractionalSet length resource).card → FractionalPair length resource)
    (fuel : ℕ) (resource : Allocation n) : (roundResources length select fuel resource).average = resource := by
  induction fuel generalizing resource with
  | zero => rfl
  | succ fuel ih =>
    unfold roundResources
    split_ifs with h
    · simp only [RoundingTree.average, ih]
      funext k
      exact updatePair_expectation length resource (select resource h).distinct
        (select resource h).interior_i (select resource h).interior_j k
    · rfl

theorem roundResources_leaves {n : ℕ} (length resource : Allocation n)
    (select : ∀ r : Allocation n, 1 < (fractionalSet length r).card → FractionalPair length r)
    (fuel : ℕ) (hbox : InBox length resource)
    (hcard : (fractionalSet length resource).card ≤ fuel + 1) :
    (roundResources length select fuel resource).ForLeaves (fun r =>
      InBox length r ∧ (∑ j, r j) = (∑ j, resource j) ∧ (fractionalSet length r).card ≤ 1) := by
  induction fuel generalizing resource with
  | zero => exact ⟨hbox, rfl, hcard⟩
  | succ fuel ih =>
    unfold roundResources
    split_ifs with h
    · let c := select resource h
      let p := resourcePair length resource c.i c.j c.interior_i c.interior_j
      have hUbox := updatePair_inBox c.distinct hbox c.interior_i c.interior_j (Or.inr rfl : p.upper = p.lower ∨ p.upper = p.upper)
      have hLbox := updatePair_inBox c.distinct hbox c.interior_i c.interior_j (Or.inl rfl : p.lower = p.lower ∨ p.lower = p.upper)
      have hUcard := updatePair_fractional_decreases c.distinct c.interior_i c.interior_j (Or.inr rfl : p.upper = p.lower ∨ p.upper = p.upper)
      have hLcard := updatePair_fractional_decreases c.distinct c.interior_i c.interior_j (Or.inl rfl : p.lower = p.lower ∨ p.lower = p.upper)
      have hUsum := updatePair_sum resource c.distinct p.upper
      have hLsum := updatePair_sum resource c.distinct p.lower
      have hU := ih (updatePair resource c.i c.j p.upper) hUbox (by omega)
      have hL := ih (updatePair resource c.i c.j p.lower) hLbox (by omega)
      constructor
      · exact (roundResources length select fuel (updatePair resource c.i c.j p.upper)).forLeaves_mono
          (fun r hr => ⟨hr.1, hr.2.1.trans hUsum, hr.2.2⟩) hU
      · exact (roundResources length select fuel (updatePair resource c.i c.j p.lower)).forLeaves_mono
          (fun r hr => ⟨hr.1, hr.2.1.trans hLsum, hr.2.2⟩) hL
    · exact ⟨hbox, rfl, le_of_not_gt h⟩

/-- Three resources terminate with at most one fractional coordinate after at
most two updates, preserving both the total and all expected coefficients. -/
theorem roundThree_contract (length resource : Allocation 3) (hbox : InBox length resource) :
    let T := roundResources length (chooseFractionalPair length) 2 resource
    T.height ≤ 2 ∧ T.average = resource ∧ T.ForLeaves (fun r =>
      InBox length r ∧ (∑ j, r j) = (∑ j, resource j) ∧ (fractionalSet length r).card ≤ 1) := by
  refine ⟨roundResources_height _ _ _ _, roundResources_average _ _ _ _, ?_⟩
  apply roundResources_leaves _ _ _ _ hbox
  exact (Finset.card_le_univ _).trans (by simp)

/-- A concrete selector for three coordinates: test 01, then 02, then 12. -/
noncomputable def selectThreePair (length resource : Allocation 3)
    (h : 1 < (fractionalSet length resource).card) : FractionalPair length resource := by
  classical
  by_cases h01 : Fractional length resource 0 ∧ Fractional length resource 1
  · exact ⟨0, 1, by decide, h01.1, h01.2⟩
  by_cases h02 : Fractional length resource 0 ∧ Fractional length resource 2
  · exact ⟨0, 2, by decide, h02.1, h02.2⟩
  have h12 : Fractional length resource 1 ∧ Fractional length resource 2 := by
    rcases Finset.one_lt_card.mp h with ⟨a, ha, b, hb, hab⟩
    fin_cases a <;> fin_cases b <;> simp_all [mem_fractionalSet]
  exact ⟨1, 2, by decide, h12.1, h12.2⟩

/-- The general mathematical rounding reduction uses at most n-1 pair updates
on every path, and preserves every coefficient through its actual lottery. -/
theorem roundResources_contract {n : ℕ} (length resource : Allocation n) (hbox : InBox length resource) :
    let T := roundResources length (chooseFractionalPair length) (n - 1) resource
    T.height ≤ n - 1 ∧ T.average = resource ∧ T.ForLeaves (fun r =>
      InBox length r ∧ (∑ j, r j) = (∑ j, resource j) ∧ (fractionalSet length r).card ≤ 1) := by
  refine ⟨roundResources_height _ _ _ _, roundResources_average _ _ _ _, ?_⟩
  apply roundResources_leaves _ _ _ _ hbox
  have he := Finset.card_le_univ (fractionalSet length resource)
  simp only [Fintype.card_fin] at he
  omega

end Blotto
