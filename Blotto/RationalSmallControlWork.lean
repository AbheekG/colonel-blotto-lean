import Blotto.RationalSmallCallbackLedger
import Blotto.RationalNestedControlWords
import Blotto.CachedControlIndexedBound

/-! The small branch's Boolean words keep one reached height certificate
through its root, uniform branch and reflected serial continuation. Encoding
and coin-body allowances include residual iterations and cap exhaustion. -/

namespace Blotto.RationalFourInput

def smallControlWordHeight (s : ℕ) : ℕ := (expressionHeightBudget s 68 + 1) * 19

theorem smallControlWordHeight_bounds (s : ℕ) :
    (expressionHeightBudget s 35 + 1) * 10 ≤ smallControlWordHeight s ∧ s ≤ smallControlWordHeight s := by
  have h35 := expressionHeightBudget_mono s (by decide : 35 ≤ 68)
  have hs := expressionHeightBudget_ge_input s 68
  unfold smallControlWordHeight
  omega

theorem FieldsHeight.smallCallback_wordsHeight {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) (hPrecision : K + 2 ≤ s) (outerBits scalarBits : Fin K → Bool)
    (cursor : i.SmallState hcase) (hCursor : i.smallCallbackInvariant hcase s cursor) :
    ((i.smallMachine hcase K outerBits scalarBits).step cursor).WordsHeight (smallControlWordHeight s) := by
  cases cursor with
  | start =>
    have hw : (WordTransition.ask i.smallWords.numerator i.smallWords.denominator i.smallWords.denominator_pos
        i.smallWords.normalized (BinaryState.upper (i.smallUniformLottery hcase).start)
        (BinaryState.lower (i.reflectedResourceSystem hcase).samplingStart) : WordTransition (i.SmallState hcase) (Fin 4 → ℚ)).WordsHeight s := h.smallWords
    exact hw.mono (smallControlWordHeight_bounds s).2
  | upper state =>
    have hw := categoricalTransition_wordsHeight (0 : Fin 9) 9 _ state hCursor
    have hMapped := WordTransition.mapValue_wordsHeight
      (fun slot => (i.smallUniformLottery hcase).point K slot scalarBits)
      ((categoricalMachine (0 : Fin 9)).step state) _ hw
    exact (WordTransition.mapState_wordsHeight (fun q => (BinaryState.upper q : i.SmallState hcase)) _ _ hMapped).mono (smallControlWordHeight_bounds s).1
  | lower state =>
    have hSystem := h.reflectedResourceSystem hs hcase
    have hs14 := hs.trans (expressionHeightBudget_ge_input s 14)
    have hPrec := hPrecision.trans (expressionHeightBudget_ge_input s 14)
    have hw := hSystem.localCallback_wordsHeight hs14 K hPrec outerBits scalarBits state hCursor
    unfold RationalNestedResourceSystem.localControlWordHeight at hw
    rw [expressionHeightBudget_comp] at hw
    have hMapped := WordTransition.mapValue_wordsHeight (RationalAffineAllocation.reflectAppend i.originalLengths).value
      (((i.reflectedResourceSystem hcase).machine K outerBits scalarBits).step state) _ hw
    exact WordTransition.mapState_wordsHeight (fun q => (BinaryState.lower q : i.SmallState hcase)) _ _ hMapped

def smallBooleanControlWork (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.smallMachine hcase K outerBits scalarBits).cachedControlWork (fun _ => true)
    (fun w => 4 * w) FixedWordCoin.bodyAllowance N bits (.state .start) pos hpos

theorem FieldsHeight.smallBooleanControlWork_bound {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) (hPrecision : K + 2 ≤ s) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.smallBooleanControlWork hcase K outerBits scalarBits N bits pos hpos ≤
      80 * smallControlWordHeight s + (24 * smallControlWordHeight s + 28) * (42 + 2 * (N - pos)) := by
  have hp := (i.smallMachine hcase K outerBits scalarBits).cachedControlWork_state_bound_under
    (i.smallCallbackInvariant hcase s) (smallControlWordHeight s)
    (h.smallCallback_wordsHeight hs hcase K hPrecision outerBits scalarBits)
    (h.smallCallback_closed hs hcase K hPrecision outerBits scalarBits)
    N bits .start (h.smallCallback_start hcase) 20 (i.smallMachine_rank hcase K outerBits scalarBits) pos hpos
  change i.smallBooleanControlWork hcase K outerBits scalarBits N bits pos hpos ≤ _ at hp
  convert hp using 1; ring

theorem FieldsHeight.smallBooleanControlWork_precision_bound {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s)
    (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.smallBooleanControlWork hcase K outerBits scalarBits N bits pos hpos ≤
      80 * smallControlWordHeight (max s (K + 2)) +
        (24 * smallControlWordHeight (max s (K + 2)) + 28) * (42 + 2 * (N - pos)) :=
  (h.mono (le_max_left s (K + 2))).smallBooleanControlWork_bound (hs.trans (le_max_left s (K + 2)))
    hcase K (le_max_right s (K + 2)) outerBits scalarBits N bits pos hpos

end Blotto.RationalFourInput
