import Blotto.RationalResourceArray
import Blotto.ActiveResourceList
import Blotto.RationalFractionalTest

/-! Native rational active-resource states. Initialization scans once, and
each update tests only the selected pair and reuses the untouched tail.
The exact real view refines the maintained resource-rounding invariants. -/

namespace Blotto
open scoped BigOperators

def rationalRetainedPair {n : ℕ} (L : Fin n → ℚ) (r : RationalResourceArray n) (a b : Fin n) : List (Fin n) :=
  [a, b].filter (rationalFractionalAt L r.allocation)

theorem rationalRetainedPair_real {n : ℕ} (L : Fin n → ℚ) (r : RationalResourceArray n) (a b : Fin n) :
    rationalRetainedPair L r a b = retainedPair (fun j => (L j : ℝ)) r.realAllocation a b := by
  classical
  unfold rationalRetainedPair retainedPair
  congr 1
  funext j
  rw [rationalFractionalAt_eq_decide]
  have he : (0 < r.allocation j ∧ r.allocation j < L j) ↔
      Fractional (fun j => (L j : ℝ)) r.realAllocation j := by
    simp only [Fractional, RationalResourceArray.realAllocation]
    norm_cast
  simp only [he]

structure RationalActiveResources {n : ℕ} (L : Fin n → ℚ) where
  resource : RationalResourceArray n
  active : List (Fin n)
  nodup : active.Nodup
  membership : ∀ j, j ∈ active ↔ 0 < resource.allocation j ∧ resource.allocation j < L j

namespace RationalActiveResources

noncomputable def realView {n : ℕ} {L : Fin n → ℚ} (s : RationalActiveResources L) :
    ActiveResourceList (fun j => (L j : ℝ)) where
  resource := s.resource.realAllocation
  active := s.active
  nodup := s.nodup
  membership := by
    intro j
    rw [s.membership j]
    simp only [Fractional, RationalResourceArray.realAllocation]
    norm_cast

def initial {n : ℕ} (L r : Fin n → ℚ) : RationalActiveResources L :=
  let resource := RationalResourceArray.ofAllocation r
  { resource := resource
    active := (List.finRange n).filter (rationalFractionalAt L resource.allocation)
    nodup := (List.nodup_finRange n).filter _
    membership := by intro j; simp [resource, RationalResourceArray.allocation_ofAllocation, List.mem_finRange] }

theorem initial_length_le {n : ℕ} (L r : Fin n → ℚ) : (initial L r).active.length ≤ n := by
  have he := List.length_filter_le (fun j => decide (0 < r j ∧ r j < L j)) (List.finRange n)
  simpa only [initial, RationalResourceArray.allocation_ofAllocation, List.length_finRange, rationalFractionalAt_function] using he

theorem selected_fractional {n : ℕ} {L : Fin n → ℚ} (s : RationalActiveResources L)
    {a b : Fin n} {tail : List (Fin n)} (he : s.active = a :: b :: tail) :
    (0 < s.resource.allocation a ∧ s.resource.allocation a < L a) ∧
      (0 < s.resource.allocation b ∧ s.resource.allocation b < L b) :=
  ⟨(s.membership a).mp (by simp [he]), (s.membership b).mp (by simp [he])⟩

def pair {n : ℕ} {L : Fin n → ℚ} (s : RationalActiveResources L)
    (a b : Fin n) (tail : List (Fin n)) (he : s.active = a :: b :: tail) : RationalRoundingPair :=
  ⟨L a, L b, s.resource.allocation a, s.resource.allocation b,
    (s.selected_fractional he).1, (s.selected_fractional he).2⟩

def update {n : ℕ} {L : Fin n → ℚ} (s : RationalActiveResources L)
      (a b : Fin n) (tail : List (Fin n)) (he : s.active = a :: b :: tail) (z : ℚ) : RationalActiveResources L :=
  let nextResource := s.resource.updatePair a b z
  { resource := nextResource
    active := rationalRetainedPair L nextResource a b ++ tail
    nodup := by
      have hactive : rationalRetainedPair L (s.resource.updatePair a b z) a b ++ tail =
          (s.realView.update a b tail he z).active := by
        rw [rationalRetainedPair_real, s.resource.realAllocation_updatePair]
        rfl
      rw [hactive]
      exact (s.realView.update a b tail he z).nodup
    membership := by
      intro j
      have hactive : rationalRetainedPair L (s.resource.updatePair a b z) a b ++ tail =
          (s.realView.update a b tail he z).active := by
        rw [rationalRetainedPair_real, s.resource.realAllocation_updatePair]
        rfl
      rw [hactive, (s.realView.update a b tail he z).membership j]
      have hreal := s.resource.realAllocation_updatePair a b z
      simp only [ActiveResourceList.update, Fractional, realView]
      rw [← hreal]
      simp only [RationalResourceArray.realAllocation]
      norm_cast }

theorem update_realView {n : ℕ} {L : Fin n → ℚ} (s : RationalActiveResources L)
    (a b : Fin n) (tail : List (Fin n)) (he : s.active = a :: b :: tail) (z : ℚ) :
    (s.update a b tail he z).realView = s.realView.update a b tail he z := by
  apply ActiveResourceList.eq_of_fields
  · exact s.resource.realAllocation_updatePair a b z
  · change rationalRetainedPair L (s.resource.updatePair a b z) a b ++ tail = _
    rw [rationalRetainedPair_real, s.resource.realAllocation_updatePair]
    rfl

theorem update_length_lt {n : ℕ} {L : Fin n → ℚ} (s : RationalActiveResources L)
    (a b : Fin n) (tail : List (Fin n)) (he : s.active = a :: b :: tail) {z : ℚ}
    (hz : z = (s.pair a b tail he).lower ∨ z = (s.pair a b tail he).upper) :
    (s.update a b tail he z).active.length < s.active.length := by
  have hr : (z : ℝ) = (s.pair a b tail he).real.lower ∨ (z : ℝ) = (s.pair a b tail he).real.upper := by
    rcases hz with rfl | rfl
    · exact Or.inl (s.pair a b tail he).lower_real
    · exact Or.inr (s.pair a b tail he).upper_real
  have hp := s.realView.update_length_lt a b tail he hr
  have ha := congrArg ActiveResourceList.active (s.update_realView a b tail he z)
  change (s.update a b tail he z).active = (s.realView.update a b tail he z).active at ha
  rw [ha]
  exact hp

theorem update_sum {n : ℕ} {L : Fin n → ℚ} (s : RationalActiveResources L)
    (a b : Fin n) (tail : List (Fin n)) (he : s.active = a :: b :: tail) (z : ℚ) :
    (∑ j, (s.update a b tail he z).resource.realAllocation j) = ∑ j, s.resource.realAllocation j :=
  s.resource.updatePair_sum (s.realView.selected_distinct he) z

theorem update_inBox {n : ℕ} {L : Fin n → ℚ} (s : RationalActiveResources L)
    (a b : Fin n) (tail : List (Fin n)) (he : s.active = a :: b :: tail) {z : ℚ}
    (hbox : InBox (fun j => (L j : ℝ)) s.resource.realAllocation)
    (hz : z = (s.pair a b tail he).lower ∨ z = (s.pair a b tail he).upper) :
    InBox (fun j => (L j : ℝ)) (s.update a b tail he z).resource.realAllocation := by
  have hr : (z : ℝ) = (s.pair a b tail he).real.lower ∨ (z : ℝ) = (s.pair a b tail he).real.upper := by
    rcases hz with rfl | rfl
    · exact Or.inl (s.pair a b tail he).lower_real
    · exact Or.inr (s.pair a b tail he).upper_real
  change InBox _ (s.resource.updatePair a b z).realAllocation
  rw [s.resource.realAllocation_updatePair]
  exact updatePair_inBox (s.realView.selected_distinct he) hbox
    (s.realView.selected_fractional he).1 (s.realView.selected_fractional he).2 hr

theorem update_expectation {n : ℕ} {L : Fin n → ℚ} (s : RationalActiveResources L)
    (a b : Fin n) (tail : List (Fin n)) (he : s.active = a :: b :: tail) (j : Fin n) :
    ((s.pair a b tail he).words.rational : ℝ) * (s.update a b tail he (s.pair a b tail he).upper).resource.realAllocation j +
      (1 - ((s.pair a b tail he).words.rational : ℝ)) *
        (s.update a b tail he (s.pair a b tail he).lower).resource.realAllocation j = s.resource.realAllocation j := by
  rw [(s.pair a b tail he).words_rational, (s.pair a b tail he).probability_real]
  change (s.pair a b tail he).real.probability * (s.resource.updatePair a b _).realAllocation j +
    (1 - (s.pair a b tail he).real.probability) * (s.resource.updatePair a b _).realAllocation j = _
  rw [s.resource.realAllocation_updatePair, s.resource.realAllocation_updatePair,
    (s.pair a b tail he).upper_real, (s.pair a b tail he).lower_real]
  exact updatePair_expectation _ _ (s.realView.selected_distinct he)
    (s.realView.selected_fractional he).1 (s.realView.selected_fractional he).2 j

end RationalActiveResources
end Blotto
