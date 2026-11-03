import Blotto.RationalTerminalProgram
import Blotto.RationalTerminalExactLaw
import Blotto.RationalGroupProgramLaw

/-! Ideal scalar averaging of the native terminal controller preserves the
three-over-two midpoint bound, including cached output and copied pivot. -/

namespace Blotto.RationalTerminalLotto
open MeasureTheory

theorem program_ideal_none {n : ℕ} (i : RationalTerminalLotto n) (h : i.pivot = none) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) :
    (i.program K outerBits scalarBits).idealLaw = i.partition.real.splitLaw
      (((i.uniformSpec (i.pivot_none h)).program i.groups_count K scalarBits).idealLaw) := by
  rw [program_refines]
  unfold programReference
  dsimp only
  split
  · exact (PreparedGroupOutput.prepare i.partition).machineIdealLaw_eq _ _
  · rename_i pivot hp
    rw [h] at hp
    cases hp

theorem program_ideal_some {n : ℕ} (i : RationalTerminalLotto n) (pivot : Fin n) (h : i.pivot = some pivot) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) :
    (i.program K outerBits scalarBits).idealLaw = i.partition.real.splitMixedLaw pivot
      (((i.mixedSpec pivot (i.pivot_some h)).program i.groups_count K outerBits scalarBits).idealLaw) := by
  rw [program_refines]
  unfold programReference
  dsimp only
  split
  · rename_i hp
    rw [h] at hp
    cases hp
  · rename_i pivot' hp
    have he : pivot' = pivot := Option.some.inj (hp.symm.trans h)
    subst pivot'
    exact (PreparedGroupOutput.prepare i.partition).machineMixedIdealLaw_eq pivot _ _

theorem exactLaw_none {n : ℕ} (i : RationalTerminalLotto n) (h : i.pivot = none) :
    i.exactLaw = i.exactUniformLaw (i.pivot_none h) := by
  unfold exactLaw
  split
  · rfl
  · rename_i pivot hp
    rw [h] at hp
    cases hp

theorem exactLaw_some {n : ℕ} (i : RationalTerminalLotto n) (pivot : Fin n) (h : i.pivot = some pivot) :
    i.exactLaw = i.exactMixedLaw pivot (i.pivot_some h) := by
  unfold exactLaw
  split
  · rename_i hp
    rw [h] at hp
    cases hp
  · rename_i pivot' hp
    have he : pivot' = pivot := Option.some.inj (hp.symm.trans h)
    subst pivot'
    rfl

noncomputable def midpointLaw {n : ℕ} (i : RationalTerminalLotto n) (K : ℕ) : Mixed n :=
  averagedLaw (fairBitLaw K) (fun outerBits => averagedLaw (fairBitLaw K)
    (fun scalarBits => (i.program K outerBits scalarBits).idealLaw) (measurable_of_countable _)) (measurable_of_countable _)

theorem midpointLaw_none {n : ℕ} (i : RationalTerminalLotto n) (h : i.pivot = none) (K : ℕ) :
    i.midpointLaw K = i.partition.real.splitLaw ((i.uniformSpec (i.pivot_none h)).midpointLaw i.groups_count K) := by
  calc
    _ = averagedLaw (fairBitLaw K) (fun _ => i.partition.real.splitLaw
        ((i.uniformSpec (i.pivot_none h)).midpointLaw i.groups_count K)) (measurable_of_countable _) := by
      apply averaged_fairBit_congr
      intro outerBits
      calc
        _ = averagedLaw (fairBitLaw K) (fun scalarBits => i.partition.real.splitLaw
            (((i.uniformSpec (i.pivot_none h)).program i.groups_count K scalarBits).idealLaw)) (measurable_of_countable _) :=
          averaged_fairBit_congr K _ _ (i.program_ideal_none h K outerBits)
        _ = _ := by
          change averagedLaw (fairBitLaw K) (fun scalarBits =>
            (((i.uniformSpec (i.pivot_none h)).program i.groups_count K scalarBits).idealLaw).map i.partition.real.split)
              (measurable_of_countable _) = _
          rw [averaged_fairBit_map K _ _ i.partition.real.measurable_split,
            RationalUniformGroupSpec.averaged_programIdeal]
          rfl
    _ = _ := averaged_fairBit_constant K _

theorem midpointLaw_some {n : ℕ} (i : RationalTerminalLotto n) (pivot : Fin n) (h : i.pivot = some pivot) (K : ℕ) :
    i.midpointLaw K = i.partition.real.splitMixedLaw pivot
      ((i.mixedSpec pivot (i.pivot_some h)).midpointLaw i.groups_count K) := by
  calc
    _ = averagedLaw (fairBitLaw K) (fun outerBits => averagedLaw (fairBitLaw K)
        (fun scalarBits => i.partition.real.splitMixedLaw pivot
          (((i.mixedSpec pivot (i.pivot_some h)).program i.groups_count K outerBits scalarBits).idealLaw))
            (measurable_of_countable _)) (measurable_of_countable _) := by
      apply averaged_fairBit_congr
      intro outerBits
      exact averaged_fairBit_congr K _ _ (i.program_ideal_some pivot h K outerBits)
    _ = averagedLaw (fairBitLaw K) (fun outerBits =>
        (averagedLaw (fairBitLaw K) (fun scalarBits =>
          ((i.mixedSpec pivot (i.pivot_some h)).program i.groups_count K outerBits scalarBits).idealLaw)
            (measurable_of_countable _)).map (i.partition.real.splitMixed pivot)) (measurable_of_countable _) := by
      apply averaged_fairBit_congr
      intro outerBits
      exact averaged_fairBit_map K _ _ (i.partition.real.measurable_splitMixed pivot)
    _ = _ := averaged_fairBit_map K _ _ (i.partition.real.measurable_splitMixed pivot)

theorem midpointLaw_CDF_error {n : ℕ} (i : RationalTerminalLotto n) (K : ℕ) :
    CDFClose (i.midpointLaw K) i.exactLaw (3 / (2 * (2 : ℝ) ^ K)) := by
  cases h : i.pivot with
  | none =>
    rw [i.midpointLaw_none h K, i.exactLaw_none h]
    exact i.partition.real.splitLaw_CDFClose _ _ (by positivity)
      ((i.uniformSpec (i.pivot_none h)).midpointLaw_CDF_error i.groups_count K)
  | some pivot =>
    rw [i.midpointLaw_some pivot h K, i.exactLaw_some pivot h]
    exact i.partition.real.splitMixedLaw_CDFClose pivot
      (by simpa only [RationalProportionalGroups.real, List.mem_toFinset] using
        i.fractional_not_in_groups pivot (i.pivot_some h)) _ _
      ((i.mixedSpec pivot (i.pivot_some h)).midpointLaw_CDF_error i.groups_count K)

end Blotto.RationalTerminalLotto
