import Blotto.Rounding
import Blotto.Boxes

/-! Pairwise resource rounding on an entire vector. No allocation coupling or
running-time claim is assumed by these state invariants. -/

namespace Blotto
open MeasureTheory Set
open scoped BigOperators

def Fractional {n : ℕ} (length resource : Allocation n) (i : Fin n) : Prop :=
  0 < resource i ∧ resource i < length i

noncomputable def fractionalSet {n : ℕ} (length resource : Allocation n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (Fractional length resource)

theorem mem_fractionalSet {n : ℕ} (length resource : Allocation n) (i : Fin n) :
    i ∈ fractionalSet length resource ↔ Fractional length resource i := by
  classical
  simp [fractionalSet]

noncomputable def updatePair {n : ℕ} (resource : Allocation n) (i j : Fin n) (z : ℝ) : Allocation n :=
  Function.update (Function.update resource i z) j (resource i + resource j - z)

theorem updatePair_i {n : ℕ} (resource : Allocation n) {i j : Fin n} (hij : i ≠ j) (z : ℝ) :
    updatePair resource i j z i = z := by simp [updatePair, hij]

theorem updatePair_j {n : ℕ} (resource : Allocation n) (i j : Fin n) (z : ℝ) :
    updatePair resource i j z j = resource i + resource j - z := by simp [updatePair]

theorem updatePair_other {n : ℕ} (resource : Allocation n) {i j k : Fin n}
    (hki : k ≠ i) (hkj : k ≠ j) (z : ℝ) : updatePair resource i j z k = resource k := by
  simp [updatePair, hki, hkj]

noncomputable def resourcePair {n : ℕ} (length resource : Allocation n) (i j : Fin n)
    (hi : Fractional length resource i) (hj : Fractional length resource j) : RoundingPair :=
  ⟨length i, length j, resource i, resource j, hi, hj⟩

theorem updatePair_inBox {n : ℕ} {length resource : Allocation n} {i j : Fin n} (hij : i ≠ j)
    (hbox : InBox length resource) (hi : Fractional length resource i) (hj : Fractional length resource j)
    {z : ℝ} (hz : z = (resourcePair length resource i j hi hj).lower ∨
      z = (resourcePair length resource i j hi hj).upper) :
    InBox length (updatePair resource i j z) := by
  have hb := (resourcePair length resource i j hi hj).branch_feasible hz
  intro k
  by_cases hki : k = i
  · subst k
    rw [updatePair_i resource hij]
    exact ⟨hb.1, hb.2.1⟩
  · by_cases hkj : k = j
    · subst k
      rw [updatePair_j]
      exact ⟨hb.2.2.1, hb.2.2.2⟩
    · rw [updatePair_other resource hki hkj]
      exact hbox k

theorem sum_update_resource {n : ℕ} (resource : Allocation n) (i : Fin n) (z : ℝ) :
    ∑ k, Function.update resource i z k = (∑ k, resource k) - resource i + z := by
  classical
  have he := Finset.sum_erase_add Finset.univ resource (Finset.mem_univ i)
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
  linarith

theorem updatePair_sum {n : ℕ} (resource : Allocation n) {i j : Fin n} (hij : i ≠ j) (z : ℝ) :
    ∑ k, updatePair resource i j z k = ∑ k, resource k := by
  classical
  unfold updatePair
  rw [sum_update_resource, sum_update_resource]
  have he : Function.update resource i z j = resource j := by simp [Ne.symm hij]
  rw [he]
  ring

theorem fractional_update_subset {n : ℕ} {length resource : Allocation n} {i j : Fin n}
    (hi : Fractional length resource i) (hj : Fractional length resource j) (z : ℝ) :
    fractionalSet length (updatePair resource i j z) ⊆ fractionalSet length resource := by
  intro k hk
  apply (mem_fractionalSet _ _ _).mpr
  by_cases hki : k = i
  · subst k
    exact hi
  · by_cases hkj : k = j
    · subst k
      exact hj
    · rw [mem_fractionalSet, Fractional, updatePair_other resource hki hkj] at hk
      exact hk

/-- Each branch removes a selected fractional coordinate, and never creates a
new fractional coordinate outside the selected pair. -/
theorem updatePair_fractional_decreases {n : ℕ} {length resource : Allocation n} {i j : Fin n}
    (hij : i ≠ j) (hi : Fractional length resource i) (hj : Fractional length resource j)
    {z : ℝ} (hz : z = (resourcePair length resource i j hi hj).lower ∨
      z = (resourcePair length resource i j hi hj).upper) :
    (fractionalSet length (updatePair resource i j z)).card < (fractionalSet length resource).card := by
  have he := (resourcePair length resource i j hi hj).branch_endpoint hz
  have hs := fractional_update_subset hi hj z
  have drop : ∃ k : Fin n, k ∈ fractionalSet length resource ∧
      k ∉ fractionalSet length (updatePair resource i j z) := by
    rcases he with h0 | hL | h0 | hL
    · refine ⟨i, (mem_fractionalSet _ _ _).mpr hi, ?_⟩
      rw [mem_fractionalSet, Fractional, updatePair_i resource hij, h0]
      simp
    · change z = length i at hL
      refine ⟨i, (mem_fractionalSet _ _ _).mpr hi, ?_⟩
      rw [mem_fractionalSet, Fractional, updatePair_i resource hij, hL]
      simp
    · refine ⟨j, (mem_fractionalSet _ _ _).mpr hj, ?_⟩
      rw [mem_fractionalSet, Fractional, updatePair_j]
      change ¬(0 < (resourcePair length resource i j hi hj).total - z ∧
        (resourcePair length resource i j hi hj).total - z < length j)
      rw [h0]
      simp
    · refine ⟨j, (mem_fractionalSet _ _ _).mpr hj, ?_⟩
      rw [mem_fractionalSet, Fractional, updatePair_j]
      change ¬(0 < (resourcePair length resource i j hi hj).total - z ∧
        (resourcePair length resource i j hi hj).total - z < length j)
      change (resourcePair length resource i j hi hj).total - z = length j at hL
      rw [hL]
      simp
  rcases drop with ⟨k, hk, hn⟩
  have hsub : fractionalSet length (updatePair resource i j z) ⊆ (fractionalSet length resource).erase k := by
    intro a ha
    apply Finset.mem_erase.mpr
    exact ⟨by intro heq; subst a; exact hn ha, hs ha⟩
  exact lt_of_le_of_lt (Finset.card_le_card hsub) (Finset.card_erase_lt_of_mem hk)

theorem updatePair_expectation {n : ℕ} (length resource : Allocation n) {i j : Fin n}
    (hij : i ≠ j) (hi : Fractional length resource i) (hj : Fractional length resource j) (k : Fin n) :
    let r := resourcePair length resource i j hi hj
    r.probability * updatePair resource i j r.upper k +
      (1 - r.probability) * updatePair resource i j r.lower k = resource k := by
  dsimp only
  by_cases hki : k = i
  · subst k
    rw [updatePair_i resource hij, updatePair_i resource hij]
    exact (resourcePair length resource i j hi hj).expected_resourceI
  · by_cases hkj : k = j
    · subst k
      rw [updatePair_j, updatePair_j]
      exact (resourcePair length resource i j hi hj).expected_resourceJ
    · rw [updatePair_other resource hki hkj, updatePair_other resource hki hkj]
      ring

end Blotto
