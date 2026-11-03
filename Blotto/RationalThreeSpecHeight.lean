import Blotto.RationalThreeInputHeight
import Blotto.RationalThreeSpec
import Blotto.RationalInterpolationCode
import Blotto.DyadicMidpointHeight

/-! Unordered lengths and every segment coordinate inherit complete height
bounds. The coordinate swap changes no word size; all bit vectors are covered. -/

namespace Blotto.RationalThreeSpecCode

def environment (i : RationalThreeSpec) : FixedArrayTable 5 ℚ := FixedArrayTable.ofFn ![i.B, i.a, i.d, i.c, i.p]

theorem ordered_environment_height (i : RationalThreeSpec) (s : ℕ)
    (hEnv : ∀ j, RationalHeight ((environment i).read j) s) :
    ∀ j, RationalHeight ((RationalThreeInputCode.environment i.orderedInput).read j) s := by
  have hB : RationalHeight i.B s := by simpa [environment, FixedArrayTable.read_ofFn] using hEnv 0
  have hA : RationalHeight i.a s := by simpa [environment, FixedArrayTable.read_ofFn] using hEnv 1
  have hD : RationalHeight i.d s := by simpa [environment, FixedArrayTable.read_ofFn] using hEnv 2
  have hC : RationalHeight i.c s := by simpa [environment, FixedArrayTable.read_ofFn] using hEnv 3
  have hP : RationalHeight i.p s := by simpa [environment, FixedArrayTable.read_ofFn] using hEnv 4
  intro j
  fin_cases j
  · simpa [RationalThreeInputCode.environment, RationalThreeSpec.orderedInput, FixedArrayTable.read_ofFn] using hB
  · simpa [RationalThreeInputCode.environment, RationalThreeSpec.orderedInput, FixedArrayTable.read_ofFn] using hA.min hD
  · simpa [RationalThreeInputCode.environment, RationalThreeSpec.orderedInput, FixedArrayTable.read_ofFn] using hA.max hD
  · simpa [RationalThreeInputCode.environment, RationalThreeSpec.orderedInput, FixedArrayTable.read_ofFn] using hC
  · simpa [RationalThreeInputCode.environment, RationalThreeSpec.orderedInput, FixedArrayTable.read_ofFn] using hP

theorem weight_height (i : RationalThreeSpec) (slot : Fin 9) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment i).read j) s) :
    RationalHeight (i.segmentLottery.weight slot) (expressionHeightBudget s 18) := by
  have h := RationalThreeInputCode.segment_weight_height i.orderedInput slot s hs (ordered_environment_height i s hEnv)
  unfold RationalThreeSpec.segmentLottery
  dsimp only
  split <;> exact h

theorem endpoint_heights (i : RationalThreeSpec) (slot : Fin 9) (j : Fin 3) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment i).read j) s) :
    RationalHeight (i.segmentLottery.P slot j) (expressionHeightBudget s 4) ∧
      RationalHeight (i.segmentLottery.Q slot j) (expressionHeightBudget s 4) := by
  have h := fun j => RationalThreeInputCode.segment_endpoint_heights i.orderedInput slot j s hs (ordered_environment_height i s hEnv)
  unfold RationalThreeSpec.segmentLottery
  dsimp only
  split
  · exact h j
  · fin_cases j
    · exact h 1
    · exact h 0
    · exact h 2

theorem point_height (i : RationalThreeSpec) (K : ℕ) (slot : Fin 9) (bits : Fin K → Bool) (j : Fin 3)
    (s : ℕ) (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight ((environment i).read j) s) :
    RationalHeight (i.segmentLottery.point K slot bits j)
      (expressionHeightBudget (max (expressionHeightBudget s 4) (K + 2)) 3) := by
  have he := endpoint_heights i slot j s hs hEnv
  let w := max (expressionHeightBudget s 4) (K + 2)
  have hP := he.1.mono (le_max_left (expressionHeightBudget s 4) (K + 2))
  have hQ := he.2.mono (le_max_left (expressionHeightBudget s 4) (K + 2))
  have ht := (dyadicMidpointSample_height K bits).mono (le_max_right (expressionHeightBudget s 4) (K + 2))
  have hw : 2 ≤ w := by dsimp [w]; omega
  exact RationalInterpolationCode.output_height _ _ _ w hw hP hQ ht

theorem point_wordWidth (i : RationalThreeSpec) (K : ℕ) (slot : Fin 9) (bits : Fin K → Bool) (j : Fin 3)
    (s : ℕ) (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight ((environment i).read j) s) :
    rationalWordWidth (i.segmentLottery.point K slot bits j) ≤
      1 + 2 * expressionHeightBudget (max (expressionHeightBudget s 4) (K + 2)) 3 :=
  rationalWordWidth_of_height (point_height i K slot bits j s hs hEnv)

theorem point_wordWidth_linear (i : RationalThreeSpec) (K : ℕ) (slot : Fin 9) (bits : Fin K → Bool) (j : Fin 3)
    (s : ℕ) (hs : 2 ≤ s) (hEnv : ∀ j, RationalHeight ((environment i).read j) s) :
    rationalWordWidth (i.segmentLottery.point K slot bits j) ≤ 512 * (s + K + 1) := by
  have h := point_wordWidth i K slot bits j s hs hEnv
  norm_num [expressionHeightBudget] at h
  omega

end Blotto.RationalThreeSpecCode
