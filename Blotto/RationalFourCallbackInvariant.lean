import Blotto.RationalSmallProcessingLedger
import Blotto.RationalLocalCategoricalWork
import Blotto.RationalFourMachine

/-! One closed invariant and one callback price cover either retained four-
variable regime. Proofs preserve actual state transitions and never clip words
or charge a source-length factor to the fixed-size local controller. -/

namespace Blotto.RationalFourInput

def fourCallbackInvariant (i : RationalFourInput) (s : ℕ) : FourSamplingState i → Prop
  | .gluing _ state => state.Bounded 81 (expressionHeightBudget s 36)
  | .small hcase state => i.smallCallbackInvariant hcase s state

def fourControlWordHeight (s : ℕ) : ℕ := (expressionHeightBudget s 68 + 1) * 82
def fourCallbackWidth (s : ℕ) : ℕ := 1 + 2 * fourControlWordHeight s

def fourCallbackBitCharge (i : RationalFourInput) (model : RationalCostModel) (copyResources : Bool)
    (K : ℕ) (outerBits : Fin K → Bool) : FourSamplingState i → ℕ
  | .gluing _ state => categoricalCallbackBitCost model state
  | .small hcase state => i.smallCallbackBitCharge hcase model copyResources K outerBits state

theorem fourCallback_widths (s : ℕ) :
    categoricalRequestWidth 81 (expressionHeightBudget s 36) ≤ fourCallbackWidth s ∧
      smallCallbackWidth s ≤ fourCallbackWidth s ∧
      (expressionHeightBudget s 36 + 1) * 82 ≤ fourControlWordHeight s ∧
      smallControlWordHeight s ≤ fourControlWordHeight s := by
  have hm := expressionHeightBudget_mono s (by decide : 36 ≤ 68)
  unfold fourCallbackWidth fourControlWordHeight smallCallbackWidth smallControlWordHeight categoricalRequestWidth
  omega

theorem FieldsHeight.fourCallback_start {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (K : ℕ) (outerBits scalarBits : Fin K → Bool) : i.fourCallbackInvariant s (i.start K outerBits scalarBits) := by
  unfold start
  split_ifs with hcase
  · exact rationalWeightList_bounded (i.gluingDescriptor hcase).weight (i.gluingDescriptor hcase).nonnegative _
      (h.gluingDescriptor hs hcase).1
  · exact h.smallCallback_start (lt_of_not_ge hcase)

theorem FieldsHeight.fourCallback_closed {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (K : ℕ) (hPrecision : K + 2 ≤ s) (outerBits scalarBits : Fin K → Bool) :
    ∀ cursor, i.fourCallbackInvariant s cursor →
      ((i.machine K outerBits scalarBits).step cursor).Postcondition (i.fourCallbackInvariant s) (fun _ => True) := by
  intro cursor hCursor
  rw [machine_refines]
  cases cursor with
  | gluing hcase state =>
    have hp := categoricalTransition_bounded (0 : Fin 81) 81 _ state hCursor
    have hm := WordTransition.mapValue_statePostcondition
      (fun slot => (i.gluingDescriptor hcase).point K slot scalarBits)
      (fun q => q.Bounded 81 (expressionHeightBudget s 36)) ((categoricalMachine (0 : Fin 81)).step state) hp
    cases ht : (i.gluingMachine hcase K scalarBits).step state with
    | done output => simp [machineReference, transition, ht, WordTransition.mapState, WordTransition.Postcondition]
    | ask a b hb hab upper lower =>
      change ((i.gluingMachine hcase K scalarBits).step state).Postcondition
        (fun q => q.Bounded 81 (expressionHeightBudget s 36)) (fun _ => True) at hm
      rw [ht] at hm
      simpa only [machineReference, transition, ht, WordTransition.mapState, WordTransition.Postcondition, fourCallbackInvariant] using hm
  | small hcase state =>
    have hp := h.smallCallback_closed hs hcase K hPrecision outerBits scalarBits state hCursor
    cases ht : (i.smallMachine hcase K outerBits scalarBits).step state with
    | done output => simp [machineReference, transition, ht, WordTransition.mapState, WordTransition.Postcondition]
    | ask a b hb hab upper lower =>
      rw [ht] at hp
      simpa only [machineReference, transition, ht, WordTransition.mapState, WordTransition.Postcondition, fourCallbackInvariant] using hp

theorem FieldsHeight.fourCallbackBitCharge_bound {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (model : RationalCostModel) (copyResources : Bool) (K : ℕ) (hPrecision : K + 2 ≤ s)
    (outerBits : Fin K → Bool) (cursor : FourSamplingState i) (hCursor : i.fourCallbackInvariant s cursor) :
    i.fourCallbackBitCharge model copyResources K outerBits cursor ≤ 659 * model.rat (fourCallbackWidth s) := by
  cases cursor with
  | gluing hcase state =>
    have hp := (categoricalCallbackBitCost_bound model state 81 _ hCursor).trans
      (Nat.mul_le_mul_left 659 (model.monotone (fourCallback_widths s).1))
    exact hp
  | small hcase state =>
    have hp := (h.smallCallbackBitCharge_bound hs hcase model copyResources K hPrecision outerBits state hCursor).trans
      (Nat.mul_le_mul_left (if copyResources then 299 else 295) (model.monotone (fourCallback_widths s).2.1))
    change i.smallCallbackBitCharge hcase model copyResources K outerBits state ≤ _
    cases copyResources <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hp <;> omega

theorem FieldsHeight.fourCallback_wordsHeight {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (K : ℕ) (hPrecision : K + 2 ≤ s) (outerBits scalarBits : Fin K → Bool)
    (cursor : FourSamplingState i) (hCursor : i.fourCallbackInvariant s cursor) :
    ((i.machine K outerBits scalarBits).step cursor).WordsHeight (fourControlWordHeight s) := by
  rw [machine_refines]
  cases cursor with
  | gluing hcase state =>
    have hp := categoricalTransition_wordsHeight (0 : Fin 81) 81 _ state hCursor
    have hm := WordTransition.mapValue_wordsHeight
      (fun slot => (i.gluingDescriptor hcase).point K slot scalarBits) ((categoricalMachine (0 : Fin 81)).step state) _ hp
    exact (WordTransition.mapState_wordsHeight (fun q => (FourSamplingState.gluing hcase q : FourSamplingState i)) _ _ hm).mono
      (fourCallback_widths s).2.2.1
  | small hcase state =>
    have hp := h.smallCallback_wordsHeight hs hcase K hPrecision outerBits scalarBits state hCursor
    exact (WordTransition.mapState_wordsHeight (fun q => (FourSamplingState.small hcase q : FourSamplingState i)) _ _ hp).mono
      (fourCallback_widths s).2.2.2

end Blotto.RationalFourInput
