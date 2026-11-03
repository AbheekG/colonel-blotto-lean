import Blotto.RationalFourSmallHeight
import Blotto.RationalFourProgram

/-! Both native ordered four-variable branches, and every shared-cap output
or fallback, inherit a linear-in-input-and-precision word-size certificate. -/

namespace Blotto.RationalFourInput

theorem FieldsHeight.machine_leaves {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    ((i.machine K outerBits scalarBits).specification (i.start K outerBits scalarBits)).decode.ForLeaves
      (fun x => ∀ j, RationalHeight (x j) (expressionHeightBudget (max s (K + 2)) 72)) := by
  unfold RationalFourInput.start
  split
  · rename_i hcase
    rw [i.gluing_specification]
    apply RationalSegmentLottery.machine_forLeaves
    intro slot j
    exact (h.gluingPoint hs hcase K scalarBits slot j).mono
      (expressionHeightBudget_mono _ (by decide : 39 ≤ 72))
  · rw [i.small_specification]
    exact h.smallMachine_leaves hs _ K outerBits scalarBits

theorem FieldsHeight.fallback {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (K : ℕ) (outerBits scalarBits : Fin K → Bool) (j : Fin 4) :
    RationalHeight (i.fallback K outerBits scalarBits j) (expressionHeightBudget (max s (K + 2)) 72) :=
  (i.machine K outerBits scalarBits).chooseLeaf_forLeaves (i.start K outerBits scalarBits) _
    (h.machine_leaves hs K outerBits scalarBits) j

theorem FieldsHeight.fixedSample {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) (j : Fin 4) :
    RationalHeight (i.fixedSample K R outerBits scalarBits choiceBits j) (expressionHeightBudget (max s (K + 2)) 72) := by
  rw [RationalFourInput.fixedSample, WordStateMachine.output_refines]
  exact WordChoiceTree.output_forLeaves _ _ _ _ _ (h.machine_leaves hs K outerBits scalarBits)
    (h.fallback hs K outerBits scalarBits) j

theorem FieldsHeight.sample {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (K : ℕ) (bits : Fin (sampleBitBudget K) → Bool) (j : Fin 4) :
    RationalHeight (i.sample K bits j) (expressionHeightBudget (max s (K + 2)) 72) :=
  h.fixedSample hs K _ _ _ _ j

theorem FieldsHeight.sample_wordWidth {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (K : ℕ) (bits : Fin (sampleBitBudget K) → Bool) (j : Fin 4) :
    rationalWordWidth (i.sample K bits j) ≤ 1 + 2 * expressionHeightBudget (max s (K + 2)) 72 :=
  rationalWordWidth_of_height (h.sample hs K bits j)

end Blotto.RationalFourInput
