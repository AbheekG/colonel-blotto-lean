import Blotto.RationalFourHeight
import Blotto.RationalFourSpecMachine

/-! Unsorted native four-variable inputs keep every coordinate's word-size
bound through the three-comparison ordering and inverse output permutation. -/

namespace Blotto.RationalFourSpec

def FieldsHeight (i : RationalFourSpec) (s : ℕ) : Prop :=
  RationalHeight i.B s ∧ (∀ j, RationalHeight (i.length j) s) ∧ RationalHeight i.ell s ∧ RationalHeight i.p s

theorem FieldsHeight.input {i : RationalFourSpec} {s : ℕ} (h : i.FieldsHeight s) : i.input.FieldsHeight s :=
  ⟨h.1, h.2.1 _, h.2.1 _, h.2.1 _, h.2.2.1, h.2.2.2⟩

theorem FieldsHeight.machine_leaves {i : RationalFourSpec} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    ((i.machine K outerBits scalarBits).specification (i.input.start K outerBits scalarBits)).decode.ForLeaves
      (fun x => ∀ j, RationalHeight (x j) (expressionHeightBudget (max s (K + 2)) 72)) := by
  rw [machine, WordStateMachine.mapped_specification]
  apply WordChoiceTree.map_forLeaves
  apply WordChoiceTree.forLeaves_mono _ _ _ _ (h.input.machine_leaves hs K outerBits scalarBits)
  intro x hx j
  rw [RationalAffineAllocation.permutation_value]
  exact hx _

theorem FieldsHeight.fallback {i : RationalFourSpec} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (K : ℕ) (outerBits scalarBits : Fin K → Bool) (j : Fin 4) :
    RationalHeight (i.fallback K outerBits scalarBits j) (expressionHeightBudget (max s (K + 2)) 72) :=
  (i.machine K outerBits scalarBits).chooseLeaf_forLeaves (i.input.start K outerBits scalarBits) _
    (h.machine_leaves hs K outerBits scalarBits) j

theorem FieldsHeight.fixedSample {i : RationalFourSpec} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (K R : ℕ) (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) (j : Fin 4) :
    RationalHeight (i.fixedSample K R outerBits scalarBits choiceBits j) (expressionHeightBudget (max s (K + 2)) 72) := by
  rw [RationalFourSpec.fixedSample, WordStateMachine.output_refines]
  exact WordChoiceTree.output_forLeaves _ _ _ _ _ (h.machine_leaves hs K outerBits scalarBits)
    (h.fallback hs K outerBits scalarBits) j

theorem FieldsHeight.sample {i : RationalFourSpec} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (K : ℕ) (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) (j : Fin 4) :
    RationalHeight (i.sample K bits j) (expressionHeightBudget (max s (K + 2)) 72) := by
  rw [RationalFourSpec.sample, RationalAffineAllocation.permutation_value]
  exact h.input.sample hs K bits _

theorem FieldsHeight.sample_wordWidth {i : RationalFourSpec} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (K : ℕ) (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) (j : Fin 4) :
    rationalWordWidth (i.sample K bits j) ≤ 1 + 2 * expressionHeightBudget (max s (K + 2)) 72 :=
  rationalWordWidth_of_height (h.sample hs K bits j)

theorem FieldsHeight.sample_wordWidth_linear {i : RationalFourSpec} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (K : ℕ) (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) (j : Fin 4) :
    rationalWordWidth (i.sample K bits j) ≤ 2 ^ 73 * (s + K + 3) := by
  have hWord := h.sample_wordWidth hs K bits j
  norm_num [expressionHeightBudget] at hWord ⊢
  omega

end Blotto.RationalFourSpec
