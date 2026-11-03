import Blotto.RationalResourceMachine
import Blotto.RationalHeightBudget
import Blotto.WordMachineFallback
import Blotto.ProbabilityWordHeight

/-! Fixed-round resource height propagation. The depth factor below is used
only for the three-coordinate phase (at most two updates), never as a substitute
for the input-lattice bound of the general n-coordinate PRG loop. -/

namespace Blotto

namespace RationalRoundingPair

def FieldsHeight (p : RationalRoundingPair) (s : ℕ) : Prop :=
  RationalHeight p.lengthI s ∧ RationalHeight p.lengthJ s ∧
    RationalHeight p.resourceI s ∧ RationalHeight p.resourceJ s

theorem FieldsHeight.endpoints {p : RationalRoundingPair} {s : ℕ} (h : p.FieldsHeight s) (hs : 2 ≤ s) :
    RationalHeight p.lower (expressionHeightBudget s 2) ∧ RationalHeight p.upper (expressionHeightBudget s 2) := by
  have hTotal : RationalHeight p.total (expressionHeightBudget s 1) := by
    have hi : RationalHeight p.resourceI (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using h.2.2.1
    have hj : RationalHeight p.resourceJ (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using h.2.2.2
    exact hi.add_level hj
  have hm1 := expressionHeightBudget_ge_input s 1
  have hLower := hTotal.sub_level (h.2.1.mono hm1)
  have hZero : RationalHeight (0 : ℚ) (expressionHeightBudget s 2) :=
    (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono (hs.trans (expressionHeightBudget_ge_input s 2))
  exact ⟨hZero.max hLower, ((h.1.mono hm1).min hTotal).mono (expressionHeightBudget_mono s (by decide : 1 ≤ 2))⟩

theorem FieldsHeight.probability {p : RationalRoundingPair} {s : ℕ} (h : p.FieldsHeight s) (hs : 2 ≤ s) :
    RationalHeight p.probability (expressionHeightBudget s 4) := by
  have he := h.endpoints hs
  have hi := h.2.2.1.mono (expressionHeightBudget_ge_input s 2)
  exact (hi.sub_level he.1).div_level (he.2.sub_level he.1)

theorem FieldsHeight.words {p : RationalRoundingPair} {s : ℕ} (h : p.FieldsHeight s) (hs : 2 ≤ s) :
    p.words.numerator < 2 ^ expressionHeightBudget s 4 ∧ p.words.denominator < 2 ^ expressionHeightBudget s 4 :=
  ProbabilityWords.ofRat_height _ _ _ (h.probability hs)

end RationalRoundingPair

namespace RationalResourceArray

def HeightAt {n : ℕ} (a : RationalResourceArray n) (s : ℕ) : Prop := ∀ j, RationalHeight (a.allocation j) s

theorem HeightAt.mono {n : ℕ} {a : RationalResourceArray n} {s t : ℕ} (h : a.HeightAt s) (hst : s ≤ t) :
    a.HeightAt t := fun j => (h j).mono hst

theorem HeightAt.updatePair {n : ℕ} {a : RationalResourceArray n} {s : ℕ} (h : a.HeightAt s)
    (i j : Fin n) (z : ℚ) (hZ : RationalHeight z (expressionHeightBudget s 2)) :
    (a.updatePair i j z).HeightAt (expressionHeightBudget s 3) := by
  have hi : RationalHeight (a.allocation i) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using h i
  have hj : RationalHeight (a.allocation j) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using h j
  have hTotal := (hi.add_level hj).mono (expressionHeightBudget_mono s (by decide : 1 ≤ 2))
  have hSecond := hTotal.sub_level hZ
  intro k
  rw [a.allocation_updatePair]
  simp only [Function.update_apply]
  split_ifs
  · exact hSecond
  · exact hZ.mono (expressionHeightBudget_mono s (by decide : 2 ≤ 3))
  · exact (h k).mono (expressionHeightBudget_ge_input s 3)

end RationalResourceArray

namespace RationalActiveResources

theorem update_height {n : ℕ} {L : Fin n → ℚ} (state : RationalActiveResources L) (s : ℕ) (hs : 2 ≤ s)
    (hL : ∀ j, RationalHeight (L j) s) (hResource : state.resource.HeightAt s)
    (a b : Fin n) (tail : List (Fin n)) (he : state.active = a :: b :: tail) (z : ℚ)
    (hZ : z = (state.pair a b tail he).lower ∨ z = (state.pair a b tail he).upper) :
    (state.update a b tail he z).resource.HeightAt (expressionHeightBudget s 3) := by
  have hPair : (state.pair a b tail he).FieldsHeight s := ⟨hL a, hL b, hResource a, hResource b⟩
  have hEndpoints := hPair.endpoints hs
  apply hResource.updatePair a b z
  rcases hZ with rfl | rfl
  · exact hEndpoints.1
  · exact hEndpoints.2

end RationalActiveResources

theorem rationalResourceStep_height {n : ℕ} {L : Fin n → ℚ} (state : RationalActiveResources L)
    (s : ℕ) (hs : 2 ≤ s) (hL : ∀ j, RationalHeight (L j) s) (hResource : state.resource.HeightAt s) :
    match rationalResourceStep state with
    | .done value => value.resource.HeightAt s
    | .ask _ _ _ _ upper lower =>
      upper.materialize.resource.HeightAt (expressionHeightBudget s 3) ∧
      lower.materialize.resource.HeightAt (expressionHeightBudget s 3) := by
  rw [rationalResourceStep_refines]
  cases state with
  | mk resource active hn hm =>
    cases active with
    | nil => exact hResource
    | cons a rest =>
      cases rest with
      | nil => exact hResource
      | cons b tail =>
        let state : RationalActiveResources L := ⟨resource, a :: b :: tail, hn, hm⟩
        let p := state.pair a b tail rfl
        exact ⟨state.update_height s hs hL hResource a b tail rfl p.upper (Or.inr rfl),
          state.update_height s hs hL hResource a b tail rfl p.lower (Or.inl rfl)⟩

theorem rationalResourceMachine_height_leaves {n : ℕ} (L : Fin n → ℚ) (C s : ℕ) (hs : 2 ≤ s)
    (hL : ∀ j, RationalHeight (L j) s) (cursor : RationalResourceCursor L)
    (hResource : cursor.materialize.resource.HeightAt s) (hRank : (rationalResourceMachine L).rank cursor ≤ C) :
    ((rationalResourceMachine L).specification cursor).decode.ForLeaves
      (fun value => value.resource.HeightAt (expressionHeightBudget s (3 * C))) := by
  induction C generalizing s cursor with
  | zero =>
    cases ht : (rationalResourceMachine L).step cursor with
    | done value =>
      have hp := rationalResourceStep_height cursor.materialize s hs hL hResource
      change (rationalResourceMachine L).step cursor = _ at ht
      change (match (rationalResourceMachine L).step cursor with
        | .done value => value.resource.HeightAt s
        | .ask _ _ _ _ upper lower => upper.materialize.resource.HeightAt (expressionHeightBudget s 3) ∧ lower.materialize.resource.HeightAt (expressionHeightBudget s 3)) at hp
      rw [ht] at hp
      rw [WordStateMachine.specification_of_done _ _ value ht]
      simpa only [WordChoiceTree.decode, AdaptiveChoiceTree.ForLeaves, Nat.mul_zero, expressionHeightBudget_zero] using hp
    | ask a b hb hab upper lower =>
      have hp := (rationalResourceMachine L).progress cursor
      rw [ht] at hp
      omega
  | succ C ih =>
    have hStep := rationalResourceStep_height cursor.materialize s hs hL hResource
    change (match (rationalResourceMachine L).step cursor with
      | .done value => value.resource.HeightAt s
      | .ask _ _ _ _ upper lower => upper.materialize.resource.HeightAt (expressionHeightBudget s 3) ∧ lower.materialize.resource.HeightAt (expressionHeightBudget s 3)) at hStep
    cases ht : (rationalResourceMachine L).step cursor with
    | done value =>
      rw [ht] at hStep
      rw [WordStateMachine.specification_of_done _ _ value ht]
      exact hStep.mono (expressionHeightBudget_ge_input s _)
    | ask a b hb hab upper lower =>
      have hp := (rationalResourceMachine L).progress cursor
      rw [ht] at hp hStep
      have hs3 := hs.trans (expressionHeightBudget_ge_input s 3)
      have hL3 := fun j => (hL j).mono (expressionHeightBudget_ge_input s 3)
      have hUpper := ih _ hs3 hL3 upper hStep.1 (by omega)
      have hLower := ih _ hs3 hL3 lower hStep.2 (by omega)
      rw [expressionHeightBudget_comp] at hUpper hLower
      rw [WordStateMachine.specification_of_ask _ _ a b hb hab upper lower ht]
      have he : 3 + 3 * C = 3 * (C + 1) := by omega
      rw [he] at hUpper hLower
      exact ⟨hUpper, hLower⟩

end Blotto
