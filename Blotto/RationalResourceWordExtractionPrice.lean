import Blotto.RationalPairWordExtractionPrice
import Blotto.RationalResourcePairBitPrice

/-! Coin-word extraction is charged once at a resource request. Its operands
are the same prepared probability register used by the native source step;
terminal states do not construct coin words. -/

namespace Blotto.RationalActiveResources

def wordExtractionBitCost {n : ℕ} {L : Fin n → ℚ} (state : RationalActiveResources L) : ℕ := by
  cases state with
  | mk resource active hn hm =>
    cases active with
    | nil => exact 0
    | cons a rest =>
      cases rest with
      | nil => exact 0
      | cons b tail =>
        let state : RationalActiveResources L := ⟨resource, a :: b :: tail, hn, hm⟩
        let p := state.pair a b tail rfl
        exact RationalPairProgram.wordExtractionBitCost p (RationalPairProgram.run p) rfl

theorem wordExtractionBitCost_bound {n : ℕ} {L : Fin n → ℚ} (model : RationalCostModel)
    (state : RationalActiveResources L) (D : ℕ) (hD : 0 < D)
    (hL : ∀ j, OnRationalLattice D (L j)) (hUnit : ∀ j, L j ≤ 1) (hState : state.resource.OnLattice D) :
    state.wordExtractionBitCost ≤ 2 * model.rat (3 + 2 * binaryWordWidth D) := by
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
        exact RationalPairProgram.wordExtractionBitCost_lattice model p (RationalPairProgram.run p) rfl hD hPair (hUnit a)

theorem wordExtractionBitCost_terminal {n : ℕ} {L : Fin n → ℚ} (state : RationalActiveResources L)
    (hTerminal : state.active.length ≤ 1) : state.wordExtractionBitCost = 0 := by
  cases state with
  | mk resource active hn hm =>
    cases active with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => rfl
      | cons b tail => simp only [List.length_cons] at hTerminal; omega

def pairRequestBitCost {n : ℕ} {L : Fin n → ℚ} (model : RationalCostModel) (state : RationalActiveResources L) : ℕ :=
  state.pairBitCost model + state.wordExtractionBitCost

theorem pairRequestBitCost_bound {n : ℕ} {L : Fin n → ℚ} (model : RationalCostModel)
    (state : RationalActiveResources L) (D : ℕ) (hD : 0 < D)
    (hL : ∀ j, OnRationalLattice D (L j)) (hUnit : ∀ j, L j ≤ 1) (hState : state.resource.OnLattice D) :
    state.pairRequestBitCost model ≤ 98 * model.rat (3 + 2 * binaryWordWidth D) := by
  have hp := state.pairBitCost_bound model D hD hL hUnit hState
  have hw := state.wordExtractionBitCost_bound model D hD hL hUnit hState
  unfold pairRequestBitCost
  omega

theorem pairRequestBitCost_terminal {n : ℕ} {L : Fin n → ℚ} (model : RationalCostModel)
    (state : RationalActiveResources L) (hTerminal : state.active.length ≤ 1) : state.pairRequestBitCost model = 0 := by
  rw [pairRequestBitCost, state.pairBitCost_terminal model hTerminal, state.wordExtractionBitCost_terminal hTerminal]

end Blotto.RationalActiveResources
namespace Blotto

def rationalResourcePairRequestCharge {n : ℕ} {L : Fin n → ℚ} (model : RationalCostModel)
    (cursor : RationalResourceCursor L) : ℕ := cursor.materialize.pairRequestBitCost model

end Blotto
