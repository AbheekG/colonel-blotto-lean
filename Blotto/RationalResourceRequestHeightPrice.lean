import Blotto.RationalResourceHeightInvariant
import Blotto.RationalResourceWordExtractionPrice

/-! Constant-round local requests use actual reached field heights. No unit
budget or fixed-lattice hypothesis is needed. These prices include the shared
pair program and canonical fields, with selected stores/readers/control separate. -/

namespace Blotto.RationalActiveResources

theorem pairBitCost_fields_bound {n : ℕ} {L : Fin n → ℚ} (model : RationalCostModel)
    (state : RationalActiveResources L) (s : ℕ) (hs : 2 ≤ s)
    (hL : ∀ j, RationalHeight (L j) s) (hResource : state.resource.HeightAt s) :
    state.pairBitCost model ≤ 96 * model.rat (32 * s + 31) := by
  cases state with
  | mk resource active hn hm =>
    cases active with
    | nil => exact Nat.zero_le _
    | cons a rest =>
      cases rest with
      | nil => exact Nat.zero_le _
      | cons b tail =>
        let state : RationalActiveResources L := ⟨resource, a :: b :: tail, hn, hm⟩
        have hPair : (state.pair a b tail rfl).FieldsHeight s := ⟨hL a, hL b, hResource a, hResource b⟩
        exact RationalPairProgram.preparationBitCost_bound model hPair hs

theorem wordExtractionBitCost_fields_bound {n : ℕ} {L : Fin n → ℚ} (model : RationalCostModel)
    (state : RationalActiveResources L) (s : ℕ) (hs : 2 ≤ s)
    (hL : ∀ j, RationalHeight (L j) s) (hResource : state.resource.HeightAt s) :
    state.wordExtractionBitCost ≤ 2 * model.rat (32 * s + 31) := by
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
        have hPair : p.FieldsHeight s := ⟨hL a, hL b, hResource a, hResource b⟩
        change RationalPairProgram.wordExtractionBitCost p (RationalPairProgram.run p) rfl ≤ _
        unfold RationalPairProgram.wordExtractionBitCost
        exact ProbabilityWords.ofRatBitCost_bound model _ _ _ (RationalPairProgram.final_wordBounds hPair hs 11)

theorem pairRequestBitCost_fields_bound {n : ℕ} {L : Fin n → ℚ} (model : RationalCostModel)
    (state : RationalActiveResources L) (s : ℕ) (hs : 2 ≤ s)
    (hL : ∀ j, RationalHeight (L j) s) (hResource : state.resource.HeightAt s) :
    state.pairRequestBitCost model ≤ 98 * model.rat (32 * s + 31) := by
  have hp := state.pairBitCost_fields_bound model s hs hL hResource
  have hw := state.wordExtractionBitCost_fields_bound model s hs hL hResource
  unfold pairRequestBitCost
  omega

end Blotto.RationalActiveResources
namespace Blotto

theorem rationalResourcePairRequestCharge_height_bound {n : ℕ} (L : Fin n → ℚ) (model : RationalCostModel)
    (C s : ℕ) (hs : 2 ≤ s) (hL : ∀ j, RationalHeight (L j) s)
    (cursor : RationalResourceCursor L) (h : rationalResourceHeightInvariant L C s cursor) :
    rationalResourcePairRequestCharge model cursor ≤ 98 * model.rat (32 * expressionHeightBudget s (3 * C) + 31) :=
  cursor.materialize.pairRequestBitCost_fields_bound model _ (hs.trans (expressionHeightBudget_ge_input s _))
    (fun j => (hL j).mono (expressionHeightBudget_ge_input s _))
    (rationalResourceHeightInvariant_resource L C s cursor h)

end Blotto
