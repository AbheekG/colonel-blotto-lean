import Blotto.RationalMergeFourHeight
import Blotto.RationalNestedResourceHeight
import Blotto.RationalFourSmallProgram

/-! The complete native atom-conditioning branch has fixed-depth output word
bounds, including both continuations, reflected resource choices and fallback.
This certifies sizes; operation counts, encodings and ownership are separate. -/

namespace Blotto.RationalFourInput

theorem FieldsHeight.originalLengths {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) (j : Fin 3) :
    RationalHeight (i.originalLengths j) s := by
  fin_cases j
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2.1

theorem FieldsHeight.reflectedResourceSystem {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell) :
    (i.reflectedResourceSystem hcase).FieldsHeight (expressionHeightBudget s 14) := by
  rw [i.reflectedResourceSystem_refines]
  have hBudget : RationalHeight i.reflectedBudget (expressionHeightBudget s 12) := h.scalar hs 7
  have hShort : RationalHeight i.shortFraction (expressionHeightBudget s 12) := h.scalar hs 4
  have hScale : RationalHeight i.scaleFraction (expressionHeightBudget s 12) := h.scalar hs 5
  have hProbability : RationalHeight i.nestedProbability (expressionHeightBudget s 12) := h.scalar hs 6
  have hm12 := expressionHeightBudget_ge_input s 12
  have hm13 := expressionHeightBudget_ge_input s 13
  have hm14 := expressionHeightBudget_ge_input s 14
  refine ⟨hBudget.mono (expressionHeightBudget_mono s (by decide : 12 ≤ 14)),
    fun j => (h.originalLengths j).mono hm14, ?_, ?_⟩
  · intro j
    exact (hShort.mul_level ((h.originalLengths j).mono hm12)).mono
      (expressionHeightBudget_mono s (by decide : 13 ≤ 14))
  · intro j
    exact (hProbability.mul_level hScale).mul_level ((h.originalLengths j).mono hm13)

theorem FieldsHeight.smallWords {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s) :
    i.smallWords.numerator < 2 ^ s ∧ i.smallWords.denominator < 2 ^ s :=
  ProbabilityWords.ofRat_height _ _ _ h.2.2.2.2.2

theorem FieldsHeight.reflectedMachine_leaves {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    ((i.reflectedMachine hcase K outerBits scalarBits).specification (i.reflectedResourceSystem hcase).samplingStart).decode.ForLeaves
      (fun x => ∀ j, RationalHeight (x j) (expressionHeightBudget (max s (K + 2)) 72)) := by
  let w := max s (K + 2)
  have hW := h.mono (le_max_left s (K + 2))
  have hw : 2 ≤ w := hs.trans (le_max_left _ _)
  have hm14 := expressionHeightBudget_ge_input w 14
  have hSystem := hW.reflectedResourceSystem hw hcase
  have hMachine := hSystem.machine_leaves (hw.trans hm14) K outerBits scalarBits
  rw [max_eq_left ((le_max_right s (K + 2)).trans hm14), expressionHeightBudget_comp] at hMachine
  rw [reflectedMachine, WordStateMachine.mapped_specification]
  apply WordChoiceTree.map_forLeaves
  apply WordChoiceTree.forLeaves_mono _ _ _ _ hMachine
  intro x hx j
  have hm71 := expressionHeightBudget_ge_input w 71
  have hValue := RationalAffineAllocation.reflectAppend_height i.originalLengths x _ (hw.trans hm71)
    (fun r => (hW.originalLengths r).mono hm71) hx j
  rw [expressionHeightBudget_comp] at hValue
  exact hValue

theorem FieldsHeight.smallMachine_leaves {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    ((i.smallMachine hcase K outerBits scalarBits).specification .start).decode.ForLeaves
      (fun x => ∀ j, RationalHeight (x j) (expressionHeightBudget (max s (K + 2)) 72)) := by
  rw [smallMachine, binaryMachine_specification]
  constructor
  · apply RationalSegmentLottery.machine_forLeaves
    intro slot j
    exact (h.smallUniformPoint hs hcase K scalarBits slot j).mono
      (expressionHeightBudget_mono _ (by decide : 38 ≤ 72))
  · exact h.reflectedMachine_leaves hs hcase K outerBits scalarBits

theorem FieldsHeight.smallFallback {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) (outerBits scalarBits : Fin K → Bool) (j : Fin 4) :
    RationalHeight (i.smallFallback hcase K outerBits scalarBits j) (expressionHeightBudget (max s (K + 2)) 72) :=
  (i.smallMachine hcase K outerBits scalarBits).chooseLeaf_forLeaves .start _
    (h.smallMachine_leaves hs hcase K outerBits scalarBits) j

theorem FieldsHeight.smallFixedSample {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell) (K R : ℕ) (outerBits scalarBits : Fin K → Bool)
    (choiceBits : Fin R → Bool) (j : Fin 4) :
    RationalHeight (i.smallFixedSample hcase K R outerBits scalarBits choiceBits j) (expressionHeightBudget (max s (K + 2)) 72) := by
  rw [RationalFourInput.smallFixedSample, WordStateMachine.output_refines]
  exact WordChoiceTree.output_forLeaves _ _ _ _ _ (h.smallMachine_leaves hs hcase K outerBits scalarBits)
    (h.smallFallback hs hcase K outerBits scalarBits) j

theorem FieldsHeight.smallSample {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) (bits : Fin (smallSampleBitBudget K) → Bool) (j : Fin 4) :
    RationalHeight (i.smallSample hcase K bits j) (expressionHeightBudget (max s (K + 2)) 72) :=
  h.smallFixedSample hs hcase K _ _ _ _ j

theorem FieldsHeight.smallSample_wordWidth {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) (bits : Fin (smallSampleBitBudget K) → Bool) (j : Fin 4) :
    rationalWordWidth (i.smallSample hcase K bits j) ≤ 1 + 2 * expressionHeightBudget (max s (K + 2)) 72 :=
  rationalWordWidth_of_height (h.smallSample hs hcase K bits j)

end Blotto.RationalFourInput
