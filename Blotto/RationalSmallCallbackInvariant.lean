import Blotto.RationalNestedCallbackInvariant
import Blotto.CachedBinaryCallbackWork

/-! The small four-variable root and both continuations retain their existing
word requests and the caller's cap. Reached-state bounds join the uniform table
and reflected local resource/terminal ledger without a new input promise. -/

namespace Blotto.RationalFourInput

def smallCallbackInvariant (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (s : ℕ) : i.SmallState hcase → Prop :=
  binaryInvariant (fun state => state.Bounded 9 (expressionHeightBudget s 35))
    ((i.reflectedResourceSystem hcase).LocalCallbackInvariant (expressionHeightBudget s 14))

def smallCallbackWidth (s : ℕ) : ℕ := categoricalRequestWidth 18 (expressionHeightBudget s 68)

def smallRootFieldBitCost (i : RationalFourInput) : ℕ :=
  ProbabilityWords.ofRatBitCost i.p ⟨i.p_pos.le, i.p_lt.le⟩

def smallCallbackBitCharge (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (model : RationalCostModel) (copyResources : Bool) (K : ℕ) (outerBits : Fin K → Bool) : i.SmallState hcase → ℕ :=
  binaryCallbackCharge i.smallRootFieldBitCost (categoricalCallbackBitCost model)
    ((i.reflectedResourceSystem hcase).localCallbackBitCharge model copyResources K outerBits)

theorem FieldsHeight.smallCallback_start {i : RationalFourInput} {s : ℕ} (_h : i.FieldsHeight s)
    (hcase : i.w < (1 - i.p) * i.ell) : i.smallCallbackInvariant hcase s .start := trivial

theorem smallCallback_widths (s : ℕ) :
    categoricalRequestWidth 9 (expressionHeightBudget s 35) ≤ smallCallbackWidth s ∧
      1 + 2 * s ≤ smallCallbackWidth s ∧
      1 + 2 * expressionHeightBudget s 15 ≤ smallCallbackWidth s := by
  have h35 := expressionHeightBudget_mono s (by decide : 35 ≤ 68)
  have h15 := expressionHeightBudget_mono s (by decide : 15 ≤ 68)
  have hs := expressionHeightBudget_ge_input s 68
  unfold smallCallbackWidth categoricalRequestWidth
  omega

theorem FieldsHeight.smallCallback_closed {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) (hPrecision : K + 2 ≤ s) (outerBits scalarBits : Fin K → Bool) :
    ∀ cursor, i.smallCallbackInvariant hcase s cursor →
      ((i.smallMachine hcase K outerBits scalarBits).step cursor).Postcondition (i.smallCallbackInvariant hcase s) (fun _ => True) := by
  have hSystem := h.reflectedResourceSystem hs hcase
  have hs14 := hs.trans (expressionHeightBudget_ge_input s 14)
  have hPrec := hPrecision.trans (expressionHeightBudget_ge_input s 14)
  apply binaryInvariant_closed i.smallWords (i.uniformMachine hcase K scalarBits) (i.reflectedMachine hcase K outerBits scalarBits)
    (i.smallUniformLottery hcase).start (i.reflectedResourceSystem hcase).samplingStart
    (fun state => state.Bounded 9 (expressionHeightBudget s 35))
    ((i.reflectedResourceSystem hcase).LocalCallbackInvariant (expressionHeightBudget s 14))
  · exact rationalWeightList_bounded (i.smallUniformLottery hcase).weight
      (i.smallUniformLottery hcase).nonnegative _ (h.smallUniformLottery hs hcase).1
  · exact hSystem.localCallback_start
  · intro state hState
    exact WordTransition.mapValue_statePostcondition
      (fun slot => (i.smallUniformLottery hcase).point K slot scalarBits)
      (fun q => q.Bounded 9 (expressionHeightBudget s 35)) ((categoricalMachine (0 : Fin 9)).step state)
      (categoricalTransition_bounded (0 : Fin 9) 9 _ state hState)
  · intro state hState
    exact WordTransition.mapValue_statePostcondition (RationalAffineAllocation.reflectAppend i.originalLengths).value
      ((i.reflectedResourceSystem hcase).LocalCallbackInvariant (expressionHeightBudget s 14))
      (((i.reflectedResourceSystem hcase).machine K outerBits scalarBits).step state)
      (hSystem.localCallback_closed hs14 K hPrec outerBits scalarBits state hState)

theorem FieldsHeight.smallRootFieldBitCost_bound {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s)
    (model : RationalCostModel) : i.smallRootFieldBitCost ≤ 2 * model.rat (smallCallbackWidth s) := by
  exact ProbabilityWords.ofRatBitCost_bound model i.p ⟨i.p_pos.le, i.p_lt.le⟩ _
    ((rationalWordWidth_of_height h.2.2.2.2.2).trans (smallCallback_widths s).2.1)

theorem FieldsHeight.smallCallbackBitCharge_bound {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (hcase : i.w < (1 - i.p) * i.ell) (model : RationalCostModel) (copyResources : Bool) (K : ℕ)
    (hPrecision : K + 2 ≤ s) (outerBits : Fin K → Bool) (cursor : i.SmallState hcase)
    (hCursor : i.smallCallbackInvariant hcase s cursor) :
    i.smallCallbackBitCharge hcase model copyResources K outerBits cursor ≤
      (if copyResources then 299 else 295) * model.rat (smallCallbackWidth s) := by
  cases cursor with
  | start =>
    have hp := h.smallRootFieldBitCost_bound model
    change i.smallRootFieldBitCost ≤ _
    cases copyResources <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
  | upper state =>
    have hp := categoricalCallbackBitCost_bound model state 9 _ hCursor
    have hPrice := model.monotone (smallCallback_widths s).1
    have hScaled := hp.trans (Nat.mul_le_mul_left 83 hPrice)
    change categoricalCallbackBitCost model state ≤ _
    cases copyResources <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
  | lower state =>
    have hSystem := h.reflectedResourceSystem hs hcase
    have hs14 := hs.trans (expressionHeightBudget_ge_input s 14)
    have hPrec := hPrecision.trans (expressionHeightBudget_ge_input s 14)
    have hp := hSystem.localCallbackBitCharge_bound hs14 model copyResources K hPrec outerBits state hCursor
    rw [expressionHeightBudget_comp] at hp
    exact hp

end Blotto.RationalFourInput
