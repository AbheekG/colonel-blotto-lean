import Blotto.RationalUniformGroupLottery
import Blotto.RationalCachedGroupSpecs
import Blotto.ProportionalCDF
import Blotto.Lotto
import Blotto.PureBoundaryEquilibria
import Blotto.GeneralPaperPositiveValueRounding

/-! The paper's equal-budget small-field branch: fully saturated lengths,
native next-fit grouping, the pair/three-variable segment lottery, and only
one dyadic midpoint parameter. Categorical implementation is joined later.
The nine-slot encoding has at most seven positive segment probabilities. -/
namespace Blotto.GeneralPaperEqualFiniteKernel
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem uniform_positive {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3) :
    (i.lottery hm).real.positiveSlots.card ≤ 7 := by
  rcases hm with rfl | rfl
  · have he : (i.lottery (Or.inl rfl)).real.positiveSlots = {0} := by
      ext j
      fin_cases j <;> norm_num [RationalUniformGroupSpec.lottery,
        RationalSegmentLottery.padRight, RationalSegmentLottery.real,
        rationalComplementaryPair, SegmentLottery.positiveSlots, Fin.addCases]
    rw [he]
    norm_num
  · change i.threeInput.segmentLottery.real.positiveSlots.card ≤ 7
    rw [i.threeInput.segmentLottery_real]
    exact i.threeInput.real.segmentLottery_positive

def terminal {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1) :
    RationalTerminalLotto n where
  B := 1
  length := fun j => 2 * v.weight j
  resource := fun j => 2 * v.weight j
  B_pos := by norm_num
  length_pos := fun j => mul_pos (by norm_num) (v.positive j)
  length_le := small
  box := fun j => ⟨(mul_pos (by norm_num) (v.positive j)).le, le_rfl⟩
  resource_sum := by rw [← Finset.mul_sum, v.sum_one]
  fractional_le := by
    classical
    unfold fractionalSet
    rw [Finset.filter_eq_empty_iff.mpr (by
      intro j _ h
      exact lt_irrefl _ h.2)]
    simp only [Finset.card_empty]
    omega

theorem no_fraction {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1) :
    ∀ j, ¬(0 < (terminal v small).resource j ∧
      (terminal v small).resource j < (terminal v small).length j) := by
  intro j
  simp only [terminal, lt_self_iff_false, and_false, not_false_eq_true]

def spec {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1) :=
  (RationalTerminalPacking.prepare (terminal v small)).uniformSpec (no_fraction v small)

def lottery {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1) :=
  (spec v small).lottery (terminal v small).groups_count

theorem positive_segments {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1) :
    (lottery v small).real.positiveSlots.card ≤ 7 :=
  uniform_positive (spec v small) (terminal v small).groups_count

noncomputable def ideal {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1) : Mixed n :=
  (terminal v small).partition.real.splitLaw (lottery v small).real.law

noncomputable def law {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1) (k : ℕ) : Mixed n :=
  (terminal v small).partition.real.splitLaw ((lottery v small).real.dyadicLaw (k + 5))

def point {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (k : ℕ) (slot : Fin 9) (fresh : Fin (k + 5) → Bool) : Fin n → ℚ :=
  (terminal v small).partition.split ((lottery v small).point (k + 5) slot fresh)

theorem endpoints {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1) :
    ∀ slot, FullBudget 1 ((lottery v small).real.P slot) ∧
      FullBudget 1 ((lottery v small).real.Q slot) := by
  have h := (spec v small).lottery_endpoints (terminal v small).groups_count
  have hB : ((spec v small).B : ℝ) = 1 := by
    change ((1 : ℚ) : ℝ) = 1
    exact Rat.cast_one
  rw [hB] at h
  exact h

theorem point_fullBudget {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (k : ℕ) (slot : Fin 9) (fresh : Fin (k + 5) → Bool) :
    FullBudget 1 (fun j => (point v small k slot fresh j : ℝ)) := by
  have hp : FullBudget ((1 : ℚ) : ℝ)
      (fun j => ((lottery v small).point (k + 5) slot fresh j : ℝ)) := by
    simpa only [Rat.cast_one] using
      (lottery v small).point_fullBudget (k + 5) (endpoints v small) slot fresh
  simpa only [Rat.cast_one, point] using
    (terminal v small).partition.split_fullBudget (B := (1 : ℚ)) hp

theorem fullBudget {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1) (k : ℕ) :
    ∀ᵐ x ∂(law v small k : Measure (Allocation n)), FullBudget 1 x :=
  (terminal v small).partition.real.splitLaw_fullBudget _
    ((lottery v small).real.dyadicLaw_fullBudget (k + 5) (endpoints v small))

theorem ideal_marginal {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1) (j : Fin n) :
    (marginal (ideal v small) j : Measure ℝ) = uniformLaw (2 * v.values.weight j) := by
  let i := terminal v small
  let s := spec v small
  have hl := s.lottery_law i.groups_count
  have hc := s.real.law_contract i.groups_count
  have hg : ∃ g, j ∈ i.partition.members g := (i.partition_covers j).mpr rfl
  rcases hg with ⟨g, hg⟩
  have hg' : j ∈ i.partition.real.members g := List.mem_toFinset.mpr hg
  have hm : ∀ a, (marginal (lottery v small).real.law a : Measure ℝ) =
      uniformLaw (i.partition.real.total a) := by
    intro a
    change (marginal (s.lottery i.groups_count).real.law a : Measure ℝ) = _
    rw [hl, hc.2 a]
    change (uniformLaw ((s.length a : ℚ) : ℝ)) = uniformLaw (i.partition.real.total a)
    congr 1
    change (((RationalTerminalPacking.prepare i).groups.read a).2 : ℝ) = i.partition.real.total a
    rw [RationalTerminalPacking.total_correct, RationalProportionalGroups.total_real]
  have h := i.partition.real.splitLaw_uniform (lottery v small).real.law hm hg'
  simpa only [ideal, i, RationalProportionalGroups.real, RationalTerminalLotto.partition,
    terminal, RationalFieldSelector.values, Rat.cast_mul, Rat.cast_ofNat] using h

theorem cdf {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1) (k : ℕ) :
    CDFClose (law v small k) (ideal v small) (1 / (2 * (2 : ℝ) ^ (k + 5))) :=
  (terminal v small).partition.real.splitLaw_CDFClose _ _ (by positivity)
    ((lottery v small).real.dyadicLaw_CDF_error (k + 5))

theorem regrets {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1) (k : ℕ) :
    Supported 1 (law v small k) ∧
      regret v.values 1 (law v small k) (law v small k) ≤ (1 / (2 : ℝ) ^ k) / 32 := by
  have hs : Supported 1 (law v small k) := (fullBudget v small k).mono fun _ h => fullBudget_feasible h
  have hi := uniform_security v.values (by norm_num : (0 : ℝ) ≤ 1)
    (ideal v small) (ideal_marginal v small)
  have he := (abs_le.mp (security_close v.values (by norm_num : (0 : ℝ) ≤ 1) (cdf v small k))).2
  have hsum : security v.values 1 (law v small k) + security v.values 1 (law v small k) ≤
      1 + (1 / (2 : ℝ) ^ k) / 32 := by
    have hp : (2 : ℝ) ^ k ≠ 0 := by positivity
    have hδ : 2 * (1 / (2 * (2 : ℝ) ^ (k + 5))) = (1 / (2 : ℝ) ^ k) / 32 := by
      rw [pow_add]
      norm_num
      field_simp
    linarith only [hi, he, hδ]
  exact ⟨hs, (regrets_le_of_security_sum v.values _ _ hs hs hsum).1⟩

end Blotto.GeneralPaperEqualFiniteKernel
