import Blotto.RationalPairLatticeBitCost
import Blotto.RationalResourceLatticeMachine

/-! The selected pair's exact register-program price, charged at the native
resource callback. Terminal states perform no pair preparation. The resource
lattice is a closed proof invariant, not a production runtime test. Deferred
resource stores and callback control are priced separately. -/

namespace Blotto.RationalActiveResources

def pairBitCost {n : ℕ} {L : Fin n → ℚ} (model : RationalCostModel) (state : RationalActiveResources L) : ℕ := by
  cases state with
  | mk resource active hn hm =>
    cases active with
    | nil => exact 0
    | cons a rest =>
      cases rest with
      | nil => exact 0
      | cons b tail =>
        let state : RationalActiveResources L := ⟨resource, a :: b :: tail, hn, hm⟩
        exact RationalPairProgram.preparationBitCost model (state.pair a b tail rfl)

theorem pairBitCost_bound {n : ℕ} {L : Fin n → ℚ} (model : RationalCostModel) (state : RationalActiveResources L)
    (D : ℕ) (hD : 0 < D) (hL : ∀ j, OnRationalLattice D (L j)) (hUnit : ∀ j, L j ≤ 1)
    (hState : state.resource.OnLattice D) :
    state.pairBitCost model ≤ 96 * model.rat (3 + 2 * binaryWordWidth D) := by
  cases state with
  | mk resource active hn hm =>
    cases active with
    | nil => exact Nat.zero_le _
    | cons a rest =>
      cases rest with
      | nil => exact Nat.zero_le _
      | cons b tail =>
        let state : RationalActiveResources L := ⟨resource, a :: b :: tail, hn, hm⟩
        let p := state.pair a b tail rfl
        have hPair : p.Lattice D := ⟨hL a, hL b, hState a, hState b⟩
        exact RationalPairProgram.preparationBitCost_lattice_sharp model p hD hPair (hUnit a) (hUnit b)

theorem pairBitCost_terminal {n : ℕ} {L : Fin n → ℚ} (model : RationalCostModel) (state : RationalActiveResources L)
    (hTerminal : state.active.length ≤ 1) : state.pairBitCost model = 0 := by
  cases state with
  | mk resource active hn hm =>
    cases active with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => rfl
      | cons b tail => simp only [List.length_cons] at hTerminal; omega

end Blotto.RationalActiveResources
namespace Blotto

def rationalResourcePairCharge {n : ℕ} {L : Fin n → ℚ} (model : RationalCostModel)
    (cursor : RationalResourceCursor L) : ℕ := cursor.materialize.pairBitCost model

def rationalResourcePairInvariant {n : ℕ} (L : Fin n → ℚ) (D : ℕ) (cursor : RationalResourceCursor L) : Prop :=
  cursor.materialize.resource.OnLattice D

theorem rationalResourcePairInvariant_closed {n : ℕ} (L : Fin n → ℚ) (D : ℕ)
    (hL : ∀ j, OnRationalLattice D (L j)) : ∀ cursor, rationalResourcePairInvariant L D cursor →
      ((rationalResourceMachine L).step cursor).Postcondition (rationalResourcePairInvariant L D) (fun _ => True) := by
  intro cursor hCursor
  have hp := rationalResourceStep_lattice D hL cursor.materialize hCursor
  unfold rationalResourceMachine rationalResourceTransition
  dsimp only
  cases he : rationalResourceStep cursor.materialize with
  | done value => trivial
  | ask a b hb hab upper lower => rw [he] at hp; exact hp

theorem rationalResourcePairInvariant_initial {n : ℕ} (L r : Fin n → ℚ) (D : ℕ)
    (hR : ∀ j, OnRationalLattice D (r j)) :
    rationalResourcePairInvariant L D (.ready (RationalActiveResources.initial L r)) := by
  intro j
  change OnRationalLattice D ((RationalResourceArray.ofAllocation r).allocation j)
  rw [RationalResourceArray.allocation_ofAllocation]
  exact hR j

end Blotto
