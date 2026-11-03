import Blotto.ResourceArray
import Blotto.ActiveResourceRounding

/-! Maintained-list rounding on array-represented resources, with an exact
refinement to the functional resource lottery. Only the selected path is run.
An explicit real-RAM primitive ledger and binary arithmetic costs are separate. -/

namespace Blotto
open scoped BigOperators

structure ArrayResourceState {n : ℕ} (L : Allocation n) where
  resource : ResourceArray n
  active : List (Fin n)
  nodup : active.Nodup
  membership : ∀ j, j ∈ active ↔ Fractional L resource.allocation j

namespace ArrayResourceState

noncomputable def view {n : ℕ} {L : Allocation n} (s : ArrayResourceState L) : ActiveResourceList L :=
  ⟨s.resource.allocation, s.active, s.nodup, s.membership⟩

noncomputable def initial {n : ℕ} (L r : Allocation n) : ArrayResourceState L where
  resource := ResourceArray.ofAllocation r
  active := (ActiveResourceList.initial L r).active
  nodup := (ActiveResourceList.initial L r).nodup
  membership := by
    rw [ResourceArray.allocation_ofAllocation]
    exact (ActiveResourceList.initial L r).membership

theorem initial_view {n : ℕ} (L r : Allocation n) : (initial L r).view = ActiveResourceList.initial L r := by
  apply ActiveResourceList.eq_of_fields
  · exact ResourceArray.allocation_ofAllocation r
  · rfl

noncomputable def update {n : ℕ} {L : Allocation n} (s : ArrayResourceState L)
    (a b : Fin n) (tail : List (Fin n)) (he : s.active = a :: b :: tail) (z : ℝ) : ArrayResourceState L where
  resource := s.resource.updatePair a b z
  active := retainedPair L (s.resource.updatePair a b z).allocation a b ++ tail
  nodup := by
    rw [s.resource.allocation_updatePair]
    exact (s.view.update a b tail he z).nodup
  membership := by
    rw [s.resource.allocation_updatePair]
    exact (s.view.update a b tail he z).membership

theorem update_view {n : ℕ} {L : Allocation n} (s : ArrayResourceState L)
    (a b : Fin n) (tail : List (Fin n)) (he : s.active = a :: b :: tail) (z : ℝ) :
    (s.update a b tail he z).view = s.view.update a b tail he z := by
  apply ActiveResourceList.eq_of_fields
  · exact s.resource.allocation_updatePair a b z
  · change retainedPair L (s.resource.updatePair a b z).allocation a b ++ tail = _
    rw [s.resource.allocation_updatePair]
    rfl

end ArrayResourceState

noncomputable def runArrayResources {n : ℕ} {L : Allocation n} :
    ℕ → ArrayResourceState L → (ℕ → Bool) → ArrayResourceState L × ℕ
  | 0, s, _ => (s, 0)
  | fuel + 1, s, choice =>
    match he : s.active with
    | [] => (s, 0)
    | [_] => (s, 0)
    | a :: b :: tail =>
      let hp := s.view.selected_fractional he
      let p := resourcePair L s.resource.allocation a b hp.1 hp.2
      let z := if choice 0 then p.upper else p.lower
      let result := runArrayResources fuel (s.update a b tail he z) (fun k => choice (k + 1))
      (result.1, result.2 + 1)

theorem runArrayResources_refinement {n : ℕ} {L : Allocation n} (fuel : ℕ)
    (s : ArrayResourceState L) (choice : ℕ → Bool) :
    (runArrayResources fuel s choice).1.view = (runActiveResources fuel s.view choice).1 ∧
      (runArrayResources fuel s choice).2 = (runActiveResources fuel s.view choice).2 := by
  induction fuel generalizing s choice with
  | zero => exact ⟨rfl, rfl⟩
  | succ fuel ih =>
    cases s with
    | mk resource active hn hm =>
      cases active with
      | nil => exact ⟨rfl, rfl⟩
      | cons a tail =>
        cases tail with
        | nil => exact ⟨rfl, rfl⟩
        | cons b rest =>
          let s : ArrayResourceState L := ⟨resource, a :: b :: rest, hn, hm⟩
          let hp := s.view.selected_fractional (rfl : s.active = a :: b :: rest)
          let p := resourcePair L s.resource.allocation a b hp.1 hp.2
          let z := if choice 0 then p.upper else p.lower
          have hi := ih (s.update a b rest rfl z) (fun k => choice (k + 1))
          rw [s.update_view] at hi
          exact ⟨hi.1, congrArg (fun k => k + 1) hi.2⟩

theorem runArrayResources_updates {n : ℕ} {L : Allocation n} (fuel : ℕ)
    (s : ArrayResourceState L) (choice : ℕ → Bool) : (runArrayResources fuel s choice).2 ≤ fuel := by
  rw [(runArrayResources_refinement fuel s choice).2]
  exact runActiveResources_updates _ _ _

theorem runArrayResources_eq_trace {n : ℕ} {L : Allocation n} (fuel : ℕ)
    (s : ArrayResourceState L) (choice : ℕ → Bool) :
    (runArrayResources fuel s choice).1.resource.allocation = (roundActiveResources fuel s.view).traceLeaf choice := by
  have he := congrArg ActiveResourceList.resource (runArrayResources_refinement fuel s choice).1
  exact he.trans (runActiveResources_eq_trace _ _ _)

end Blotto
