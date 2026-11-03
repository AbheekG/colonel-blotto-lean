import Blotto.RationalThreeSpecPreparation
import Blotto.RationalNestedSpecPreparation
import Blotto.WordTransitionAdditionalPost
import Blotto.RationalGroupProgramHeight
import Blotto.RationalSegmentDecodedEmission
import Blotto.CachedControlIndexedBound
import Blotto.RationalResourceFieldWords

/-! Both actual uniform group cases retain separate lottery construction for
machine/start, all starting weight-list words and indexed sampling work.
Packed input derivation, outer output routes and metadata/backend are separate. -/

namespace Blotto.RationalUniformGroupSpec
open scoped BigOperators

noncomputable def lotteryPreparationBitCost {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3)
    (model : RationalCostModel) : ℕ := by
  by_cases h2 : m = 2
  · subst m
    exact 2 * (PreparedSegmentDescriptor.prepare (i.lottery hm)).payloadBitCost
  · have h3 : m = 3 := hm.resolve_left h2
    subst m
    exact 2 * RationalThreeSpecCode.inputFieldCopyBitCost i.threeInput +
      RationalThreeSpecCode.preparedSpecBitCost model i.threeInput

theorem FieldsHeight.lotteryPreparationBitCost_bound {m : ℕ} {i : RationalUniformGroupSpec m} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hm : m = 2 ∨ m = 3) (model : RationalCostModel) :
    i.lotteryPreparationBitCost hm model ≤ 2930 * model.rat (1 + 2 * expressionHeightBudget s 18) := by
  rcases hm with rfl | rfl
  · have hp := (PreparedSegmentDescriptor.prepare (i.lottery (Or.inl rfl))).payloadBitCost_bound _ (h.lottery hs (Or.inl rfl))
    have hw := hp.trans (Nat.mul_le_mul_left 45 (model.word_le _))
    change 2 * (PreparedSegmentDescriptor.prepare (i.lottery (Or.inl rfl))).payloadBitCost ≤ _
    omega
  · have hEnv := h.three_environment hs
    have hCopy := (RationalThreeSpecCode.inputFieldCopyBitCost_bound model i.threeInput s hEnv).trans
      (Nat.mul_le_mul_left 5 (model.monotone (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (expressionHeightBudget_ge_input s 18)) 1)))
    have hPrep := RationalThreeSpecCode.preparedSpecBitCost_bound model i.threeInput s hs hEnv
    change 2 * RationalThreeSpecCode.inputFieldCopyBitCost i.threeInput +
      RationalThreeSpecCode.preparedSpecBitCost model i.threeInput ≤ _
    omega

def startWeightBitCost {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3) : ℕ :=
  2 * ∑ slot : Fin 9, rationalWordWidth ((i.lottery hm).weight slot)

theorem FieldsHeight.startWeightBitCost_bound {m : ℕ} {i : RationalUniformGroupSpec m} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hm : m = 2 ∨ m = 3) (model : RationalCostModel) :
    i.startWeightBitCost hm ≤ 18 * model.rat (1 + 2 * expressionHeightBudget s 18) := by
  have hp : (∑ slot : Fin 9, rationalWordWidth ((i.lottery hm).weight slot)) ≤
      9 * model.rat (1 + 2 * expressionHeightBudget s 18) := by
    calc
      _ ≤ ∑ _slot : Fin 9, model.rat (1 + 2 * expressionHeightBudget s 18) := Finset.sum_le_sum (fun slot _ =>
        (rationalWordWidth_of_height ((h.lottery hs hm).1 slot)).trans (model.word_le _))
      _ = _ := by simp
  unfold startWeightBitCost
  omega

def controlWordHeight (s : ℕ) : ℕ := (expressionHeightBudget s 18 + 1) * 10

def booleanControlWork {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.program hm K scalarBits).machine.cachedControlWork (fun _ => true) (fun w => 4 * w) FixedWordCoin.bodyAllowance
    N bits (.state (i.program hm K scalarBits).start) pos hpos

theorem FieldsHeight.booleanControlWork_bound {m : ℕ} {i : RationalUniformGroupSpec m} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hm : m = 2 ∨ m = 3) (K : ℕ) (scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.booleanControlWork hm K scalarBits N bits pos hpos ≤
      32 * controlWordHeight s + (24 * controlWordHeight s + 28) * (18 + 2 * (N - pos)) := by
  let l := i.lottery hm
  have hStart := rationalWeightList_bounded l.weight l.nonnegative _ (h.lottery hs hm).1
  have hClosed : ∀ state : CategoricalState (Fin 9), state.Bounded 9 (expressionHeightBudget s 18) →
      ((l.machine 0 K scalarBits).step state).Postcondition (fun q => q.Bounded 9 (expressionHeightBudget s 18)) (fun _ => True) := by
    intro state hState
    exact WordTransition.mapValue_statePostcondition (fun slot => l.point K slot scalarBits)
      (fun q => q.Bounded 9 (expressionHeightBudget s 18)) ((categoricalMachine (0 : Fin 9)).step state)
      (categoricalTransition_bounded (0 : Fin 9) 9 _ state hState)
  have hWords : ∀ state : CategoricalState (Fin 9), state.Bounded 9 (expressionHeightBudget s 18) →
      ((l.machine 0 K scalarBits).step state).WordsHeight (controlWordHeight s) := by
    intro state hState
    exact WordTransition.mapValue_wordsHeight (fun slot => l.point K slot scalarBits)
      ((categoricalMachine (0 : Fin 9)).step state) _ (categoricalTransition_wordsHeight (0 : Fin 9) 9 _ state hState)
  have hp := (l.machine 0 K scalarBits).cachedControlWork_state_bound_under _ _ hWords hClosed N bits l.start hStart
    8 (le_of_eq (l.machine_rank 0 K scalarBits)) pos hpos
  have he : 4 * controlWordHeight s * 8 + (24 * controlWordHeight s + 28) * (2 * 8 + 2 * (N - pos) + 2) =
    32 * controlWordHeight s + (24 * controlWordHeight s + 28) * (18 + 2 * (N - pos)) := by ring
  exact hp.trans_eq he

noncomputable def completeProcessingAllowance {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3)
    (model : RationalCostModel) (primitive : ℕ → ℕ) (K : ℕ) (scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  2 * i.lotteryPreparationBitCost hm model + i.startWeightBitCost hm +
    (i.lottery hm).dataAndCallbackBitWork model primitive 0 K scalarBits N bits pos hpos +
      i.booleanControlWork hm K scalarBits N bits pos hpos

def processingWidth (s : ℕ) : ℕ := 1 + 2 * expressionHeightBudget s 23

theorem processingWidth_categorical (s : ℕ) :
    categoricalRequestWidth 9 (expressionHeightBudget s 18) ≤ processingWidth s := by
  have h23 : expressionHeightBudget s 23 = 32 * expressionHeightBudget s 18 + 31 := by
    rw [show 23 = 18 + 5 by decide, ← expressionHeightBudget_comp]
    change (expressionHeightBudget s 18 + 1) * 32 - 1 = _
    omega
  unfold categoricalRequestWidth processingWidth
  omega

theorem FieldsHeight.completeProcessingAllowance_bound {m : ℕ} {i : RationalUniformGroupSpec m} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hm : m = 2 ∨ m = 3) (model : RationalCostModel) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.completeProcessingAllowance hm model primitive K scalarBits N bits pos hpos ≤
      RationalNestedInput.preparationNumericBitWork c K + 6675 * model.rat (processingWidth (max s (K + 2))) +
        32 * controlWordHeight (max s (K + 2)) +
          (24 * controlWordHeight (max s (K + 2)) + 28) * (18 + 2 * (N - pos)) := by
  let w := max s (K + 2)
  let price := model.rat (processingWidth w)
  have hW := h.mono (le_max_left s (K + 2))
  have hw := hs.trans (le_max_left s (K + 2))
  have h18 : model.rat (1 + 2 * expressionHeightBudget w 18) ≤ price := model.heightPrice_mono (le_refl w) (by decide)
  have hPrep := (hW.lotteryPreparationBitCost_bound hw hm model).trans (Nat.mul_le_mul_left 2930 h18)
  have hStart := (hW.startWeightBitCost_bound hw hm model).trans (Nat.mul_le_mul_left 18 h18)
  have hData := (hW.lottery hw hm).dataAndCallbackBitWork_bound (hw.trans (expressionHeightBudget_ge_input w 18))
    model primitive c hPrimitive 0 K scalarBits N bits pos hpos
  rw [max_eq_left ((le_max_right s (K + 2)).trans (expressionHeightBudget_ge_input w 18)), expressionHeightBudget_comp] at hData
  have hCat : model.rat (categoricalRequestWidth 9 (expressionHeightBudget w 18)) ≤ price := model.monotone (processingWidth_categorical w)
  have hMid : model.rat (1 + 2 * expressionHeightBudget (K + 2) 3) ≤ price := model.heightPrice_mono (le_max_right s (K + 2)) (by decide : 3 ≤ 23)
  have hPoint : model.rat (1 + 2 * expressionHeightBudget w 21) ≤ price := model.heightPrice_mono (le_refl w) (by decide)
  have hm3 : m ≤ 3 := by rcases hm with hm | hm <;> omega
  have hControl := hW.booleanControlWork_bound hw hm K scalarBits N bits pos hpos
  change (i.lottery hm).dataAndCallbackBitWork model primitive 0 K scalarBits N bits pos hpos ≤
    747 * model.rat (categoricalRequestWidth 9 (expressionHeightBudget w 18)) +
      (RationalNestedInput.preparationNumericBitWork c K + 11 * model.rat (1 + 2 * expressionHeightBudget (K + 2) 3) +
        13 * m * model.rat (1 + 2 * expressionHeightBudget w 21)) at hData
  change i.completeProcessingAllowance hm model primitive K scalarBits N bits pos hpos ≤
    RationalNestedInput.preparationNumericBitWork c K + 6675 * price +
      32 * controlWordHeight w + (24 * controlWordHeight w + 28) * (18 + 2 * (N - pos))
  unfold completeProcessingAllowance
  nlinarith

end Blotto.RationalUniformGroupSpec
