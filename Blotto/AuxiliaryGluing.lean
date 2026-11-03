import Blotto.LotteryNormalization
import Blotto.RestrictedUniform

/-! An explicit conditional gluing measure. All conditional weights and
allocation maps come from the first finite segment lottery. -/

namespace Blotto
open MeasureTheory Set Filter
open scoped BigOperators

structure AuxiliaryGluing (n m k : ℕ) where
  first : SegmentLottery n k
  second : Mixed m
  firstProbe : AffineProbe n
  secondProbe : AffineProbe m
  d : ℝ
  d_pos : 0 < d
  first_uniform : Measure.map firstProbe.value (first.law : Measure (Allocation n)) = uniformLaw d
  second_uniform : Measure.map secondProbe.value (second : Measure (Allocation m)) = uniformLaw d
  first_P_range : ∀ i, 0 ≤ firstProbe.value (first.P i) ∧ firstProbe.value (first.P i) ≤ d
  first_Q_range : ∀ i, 0 ≤ firstProbe.value (first.Q i) ∧ firstProbe.value (first.Q i) ≤ d

namespace AuxiliaryGluing

noncomputable def pairedPoint {n m k : ℕ} (G : AuxiliaryGluing n m k) (i : Fin k) (y : Allocation m) :
    Allocation n × Allocation m := (G.first.pointAt G.firstProbe i (G.secondProbe.value y), y)

theorem measurable_pairedPoint {n m k : ℕ} (G : AuxiliaryGluing n m k) (i : Fin k) : Measurable (G.pairedPoint i) :=
  ((G.first.measurable_pointAt G.firstProbe i).comp G.secondProbe.measurable).prodMk measurable_id

noncomputable def cell {n m k : ℕ} (G : AuxiliaryGluing n m k) (i : Fin k) : Set (Allocation m) :=
  G.secondProbe.value ⁻¹' G.first.auxiliaryInterval G.firstProbe i

theorem measurable_cell {n m k : ℕ} (G : AuxiliaryGluing n m k) (i : Fin k) : MeasurableSet (G.cell i) :=
  measurableSet_Icc.preimage G.secondProbe.measurable

noncomputable def rawLaw {n m k : ℕ} (G : AuxiliaryGluing n m k) : Measure (Allocation n × Allocation m) :=
  Measure.sum fun i => ENNReal.ofReal (G.first.conditionalWeight G.firstProbe G.d i) •
    Measure.map (G.pairedPoint i) ((G.second : Measure (Allocation m)).restrict (G.cell i))

/-- The first whole allocation marginal is restored exactly by inverting each
source segment against the restricted common uniform. -/
theorem rawLaw_fst {n m k : ℕ} (G : AuxiliaryGluing n m k) :
    Measure.map Prod.fst G.rawLaw = (G.first.law : Measure (Allocation n)) := by
  rw [rawLaw, Measure.map_sum measurable_fst.aemeasurable, G.first.law_measure]
  congr 1
  funext i
  rw [Measure.map_smul _ measurable_fst.aemeasurable,
    Measure.map_map measurable_fst (G.measurable_pairedPoint i)]
  have he : Prod.fst ∘ G.pairedPoint i = G.first.pointAt G.firstProbe i ∘ G.secondProbe.value := rfl
  rw [he, ← Measure.map_map (G.first.measurable_pointAt G.firstProbe i) G.secondProbe.measurable]
  have hI : MeasurableSet (G.first.auxiliaryInterval G.firstProbe i) := measurableSet_Icc
  rw [cell, ← Measure.restrict_map G.secondProbe.measurable hI, G.second_uniform]
  exact G.first.reconstruct_segment G.firstProbe G.d_pos G.first_uniform i (G.first_P_range i) (G.first_Q_range i)

noncomputable def conditionalDensity {n m k : ℕ} (G : AuxiliaryGluing n m k) (i : Fin k) : Allocation m → ENNReal :=
  (G.cell i).indicator (fun _ => ENNReal.ofReal (G.first.conditionalWeight G.firstProbe G.d i))

theorem measurable_conditionalDensity {n m k : ℕ} (G : AuxiliaryGluing n m k) (i : Fin k) :
    Measurable (G.conditionalDensity i) := measurable_const.indicator (G.measurable_cell i)

theorem conditionalDensity_eq {n m k : ℕ} (G : AuxiliaryGluing n m k) (i : Fin k) (y : Allocation m) :
    G.conditionalDensity i y = ENNReal.ofReal G.d * G.first.slotDensity G.firstProbe i (G.secondProbe.value y) := by
  by_cases hy : y ∈ G.cell i
  · have hcoeff : G.first.conditionalWeight G.firstProbe G.d i = G.d *
        (G.first.weight i / |G.firstProbe.value (G.first.Q i) - G.firstProbe.value (G.first.P i)|) := by
      dsimp [SegmentLottery.conditionalWeight]; ring
    simp only [conditionalDensity, indicator_of_mem hy]
    rw [hcoeff, ENNReal.ofReal_mul (le_of_lt G.d_pos)]
    change _ = ENNReal.ofReal G.d *
      (intervalDensity _ _ _ (G.secondProbe.value y))
    have hz : G.secondProbe.value y ∈ Icc
        (min (G.firstProbe.value (G.first.P i)) (G.firstProbe.value (G.first.Q i)))
        (max (G.firstProbe.value (G.first.P i)) (G.firstProbe.value (G.first.Q i))) := hy
    simp only [intervalDensity, indicator_of_mem hz]
  · have hz : G.secondProbe.value y ∉ Icc
        (min (G.firstProbe.value (G.first.P i)) (G.firstProbe.value (G.first.Q i)))
        (max (G.firstProbe.value (G.first.P i)) (G.firstProbe.value (G.first.Q i))) := hy
    simp only [conditionalDensity, indicator_of_notMem hy, SegmentLottery.slotDensity,
      intervalDensity, indicator_of_notMem hz, mul_zero]

theorem conditionalDensity_total {n m k : ℕ} (G : AuxiliaryGluing n m k) :
    (∑' i, G.conditionalDensity i) =ᵐ[(G.second : Measure (Allocation m))] (fun _ => 1) := by
  have h := G.first.conditionalDensity_sampled G.firstProbe G.second G.secondProbe G.d_pos
    G.first_uniform G.second_uniform
  apply h.mono
  intro y hy
  have he : (∑' i, G.conditionalDensity i) y = ENNReal.ofReal G.d * G.first.auxiliaryDensity G.firstProbe (G.secondProbe.value y) := by
    simp only [tsum_fintype, Finset.sum_apply, G.conditionalDensity_eq, SegmentLottery.auxiliaryDensity,
      ← Finset.mul_sum]
  exact he.trans hy

/-- The second whole allocation marginal is unchanged. Conditional weights
normalize under its actual sampled auxiliary coordinate. -/
theorem rawLaw_snd {n m k : ℕ} (G : AuxiliaryGluing n m k) :
    Measure.map Prod.snd G.rawLaw = (G.second : Measure (Allocation m)) := by
  rw [rawLaw, Measure.map_sum measurable_snd.aemeasurable]
  have he : (fun i => Measure.map Prod.snd
      (ENNReal.ofReal (G.first.conditionalWeight G.firstProbe G.d i) •
        Measure.map (G.pairedPoint i) ((G.second : Measure (Allocation m)).restrict (G.cell i)))) =
      (fun i => (G.second : Measure (Allocation m)).withDensity (G.conditionalDensity i)) := by
    funext i
    rw [Measure.map_smul _ measurable_snd.aemeasurable,
      Measure.map_map measurable_snd (G.measurable_pairedPoint i)]
    have hid : Prod.snd ∘ G.pairedPoint i = id := rfl
    rw [hid, Measure.map_id, conditionalDensity, withDensity_indicator (G.measurable_cell i), withDensity_const]
  rw [he, ← withDensity_tsum (fun i => G.measurable_conditionalDensity i),
    withDensity_congr_ae G.conditionalDensity_total, withDensity_const, one_smul]

/-- Normalize the constructed joint measure using its first probability marginal. -/
theorem rawLaw_probability {n m k : ℕ} (G : AuxiliaryGluing n m k) : IsProbabilityMeasure G.rawLaw := by
  constructor
  have he := congrArg (fun μ : Measure (Allocation n) => μ univ) G.rawLaw_fst
  rw [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ] at he
  exact he.trans measure_univ

noncomputable def jointLaw {n m k : ℕ} (G : AuxiliaryGluing n m k) : ProbabilityMeasure (Allocation n × Allocation m) :=
  ⟨G.rawLaw, G.rawLaw_probability⟩

end AuxiliaryGluing
end Blotto
