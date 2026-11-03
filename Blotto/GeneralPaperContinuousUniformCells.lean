import Blotto.GeneralPaperContinuousArcMinimum
import Blotto.GeneralPaperRealCumulativeChoiceLaw

/-! A continuous unit-uniform shift selects equal half-open cells with
the exact uniform finite law. All cell boundaries are a null set. The
categorical selector here is an erased analysis device, not a new sampler. -/
namespace Blotto.GeneralPaperContinuousUniformCells
open MeasureTheory Set Filter
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

noncomputable def index (D : ℕ) (hD : 0 < D) (u : ℝ) : Fin D :=
  (GeneralPaperRealCumulativeChoice.manyRun (fun _ : Fin D => 1/(D : ℝ)) hD 0 u).value

theorem measurable_index (D : ℕ) (hD : 0 < D) : Measurable (index D hD) :=
  GeneralPaperRealCumulativeChoice.manyRun_measurable _ hD _

theorem index_law (D : ℕ) (hD : 0 < D) :
    Measure.map (index D hD) (unitUniform : Measure ℝ) =
      (probabilityMixture (fun _ : Fin D => 1/(D : ℝ))
        (fun i => RealThresholdChoice.pointLaw i) (fun _ => by positivity)
        (uniformWeights_sum hD) : Measure (Fin D)) :=
  GeneralPaperRealCumulativeChoice.manyRun_law _ hD (fun _ => by positivity) (uniformWeights_sum hD) _

theorem lower_constant (k : ℕ) (c : ℝ) (i : Fin (k+1)) :
    GeneralPaperRealCumulativeChoice.lower k (fun _ => c) i = (i.val : ℝ)*c := by
  induction k with
  | zero =>
    have he : i = 0 := Fin.ext (by omega)
    subst i
    simp [GeneralPaperRealCumulativeChoice.lower]
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [GeneralPaperRealCumulativeChoice.lower]
    · simp only [GeneralPaperRealCumulativeChoice.lower, Fin.cases_succ, ih,
        Fin.val_succ, Nat.cast_add, Nat.cast_one]
      ring

theorem index_fiber (D : ℕ) (hD : 0 < D) (u : ℝ) (hu : u ∈ Ico 0 1) (i : Fin D) :
    index D hD u = i ↔ u ∈ Ico ((i.val : ℝ)/D) (((i.val : ℝ)+1)/D) := by
  let h : D-1+1 = D := Nat.sub_add_cancel hD
  let w : Fin (D-1+1) → ℝ := fun _ => 1/(D : ℝ)
  have hSum : ∑ a, w a = 1 := by
    simp only [w, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, h]
    exact mul_one_div_cancel (by exact_mod_cast hD.ne')
  have hf := GeneralPaperRealCumulativeChoice.fiber (D-1) w (fun _ => by positivity)
    u (by rw [hSum]; exact hu) (i.cast h.symm)
  have he : index D hD u = i ↔
      GeneralPaperRealCumulativeChoice.select (D-1) w u = i.cast h.symm := by
    change (GeneralPaperRealCumulativeChoice.run (D-1) w 0 u).value.cast h = i ↔ _
    rw [GeneralPaperRealCumulativeChoice.run_data]
    constructor <;> intro he <;> apply Fin.ext <;>
      exact congrArg (fun j => j.val) he
  rw [he, hf]
  simp only [w, lower_constant, Fin.val_cast, mul_one_div, ← add_div]

theorem interior_ae (D : ℕ) (hD : 0 < D) :
    ∀ᵐ u ∂(unitUniform : Measure ℝ),
      ((index D hD u).val : ℝ) < (D : ℝ)*u ∧
        (D : ℝ)*u < ((index D hD u).val : ℝ)+1 := by
  have hSingle (i : Fin (D+1)) : ∀ᵐ u ∂(unitUniform : Measure ℝ), u ≠ (i.val : ℝ)/D := by
    rw [ae_iff]
    simp only [not_not]
    change uniformLaw 1 {((i.val : ℝ)/D)} = 0
    exact uniform_singleton 1 _
  have hAll : ∀ᵐ u ∂(unitUniform : Measure ℝ), ∀ i : Fin (D+1), u ≠ (i.val : ℝ)/D :=
    ae_all_iff.mpr hSingle
  filter_upwards [unitUniform_supported, hAll] with u hu hNe
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hu1 : u < 1 := by
    have hn := hNe ⟨D, by omega⟩
    have he : (D : ℝ)/(D : ℝ) = 1 := div_self hDR.ne'
    rw [he] at hn
    exact lt_of_le_of_ne hu.2 hn
  let i := index D hD u
  have hf := (index_fiber D hD u ⟨hu.1, hu1⟩ i).mp rfl
  have hLower : (i.val : ℝ)/D < u :=
    lt_of_le_of_ne hf.1 (Ne.symm (hNe ⟨i.val, by omega⟩))
  constructor
  · exact (div_lt_iff₀ hDR).mp hLower |>.trans_eq (mul_comm u (D : ℝ))
  · simpa only [mul_comm] using (lt_div_iff₀ hDR).mp hf.2

theorem averaged_laws {n : ℕ} (D : ℕ) (hD : 0 < D) (laws : Fin D → Mixed n) :
    averagedLaw unitUniform (fun u => laws (index D hD u))
      ((measurable_of_countable (fun i => (laws i : Measure (Allocation n)))).comp (measurable_index D hD)) =
      GeneralPaperUniformRowLaw.mixture hD laws := by
  let g := fun i : Fin D => (laws i : Measure (Allocation n))
  have hg : Measurable g := measurable_of_countable _
  have hTransport : (unitUniform : Measure ℝ).bind (fun u => g (index D hD u)) =
      (Measure.map (index D hD) (unitUniform : Measure ℝ)).bind g := by
    apply Measure.ext
    intro A hA
    have hgi : Measurable (fun u => g (index D hD u)) := hg.comp (measurable_index D hD)
    rw [Measure.bind_apply hA hgi.aemeasurable,
      Measure.bind_apply hA hg.aemeasurable]
    have hgA : Measurable (fun i : Fin D => (g i) A) := (Measure.measurable_coe hA).comp hg
    exact (lintegral_map hgA (measurable_index D hD)).symm
  apply ProbabilityMeasure.toMeasure_injective
  change (unitUniform : Measure ℝ).bind (fun u => g (index D hD u)) = _
  rw [hTransport, index_law]
  change (mixtureMeasure (fun _ : Fin D => 1/(D : ℝ))
    (fun i => RealThresholdChoice.pointLaw i)).bind g = _
  rw [mixtureMeasure, Measure.bind_sum _ _ hg.aemeasurable]
  change Measure.sum _ = Measure.sum _
  congr 1
  funext i
  rw [Measure.bind_smul _ _ hg.aemeasurable]
  change ENNReal.ofReal (1/(D : ℝ)) • (Measure.dirac i).bind g = _
  rw [Measure.dirac_bind hg]

end Blotto.GeneralPaperContinuousUniformCells
