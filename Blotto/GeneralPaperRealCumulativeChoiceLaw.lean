import Blotto.GeneralPaperRealCumulativeChoice

/-! Exact one-uniform categorical law of the cumulative scan. Half-open
intervals handle zero weights; the singleton endpoint of the source uniform
has zero measure. No independent uniform is read on a scan continuation. -/
namespace Blotto.GeneralPaperRealCumulativeChoice
open MeasureTheory Set
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 700000

theorem unit_measure : (unitUniform : Measure ℝ) = volume.restrict (Ico 0 1) := by
  change uniformLaw 1 = _
  simp only [uniformLaw, ENNReal.ofReal_one, inv_one, one_smul]
  exact (Measure.restrict_congr_set Ico_ae_eq_Icc).symm

theorem fiber_interval (k : ℕ) (w : Fin (k + 1) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : ∑ i, w i = 1) (i : Fin (k + 1)) :
    select k w ⁻¹' {i} ∩ Ico 0 1 = Ico (lower k w i) (lower k w i + w i) := by
  ext u
  constructor
  · intro h
    exact (fiber k w hw u (by rw [hs]; exact h.2) i).mp h.1
  · intro h
    have h0 := lower_nonnegative k w hw i
    have h1 := upper_le_sum k w hw i
    rw [hs] at h1
    have hu : u ∈ Ico 0 1 := ⟨h0.trans h.1, h.2.trans_le h1⟩
    exact ⟨(fiber k w hw u (by rw [hs]; exact hu) i).mpr h, hu⟩

theorem singleton_mass (k : ℕ) (w : Fin (k + 1) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : ∑ i, w i = 1) (i : Fin (k + 1)) :
    Measure.map (select k w) (unitUniform : Measure ℝ) {i} = ENNReal.ofReal (w i) := by
  rw [Measure.map_apply (measurable_select k w) (measurableSet_singleton i), unit_measure,
    Measure.restrict_apply ((measurableSet_singleton i).preimage (measurable_select k w)),
    fiber_interval k w hw hs i, Real.volume_Ico]
  congr 1
  ring

theorem law (k : ℕ) (w : Fin (k + 1) → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) :
    Measure.map (select k w) (unitUniform : Measure ℝ) =
      (probabilityMixture w (fun i => RealThresholdChoice.pointLaw i) hw hs : Measure (Fin (k + 1))) := by
  apply Measure.ext_of_singleton
  intro i
  rw [singleton_mass k w hw hs]
  simp [probabilityMixture, mixtureMeasure, RealThresholdChoice.pointLaw, Pi.single_apply]

theorem run_law (k : ℕ) (w : Fin (k + 1) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : ∑ i, w i = 1) (address : ℕ) :
    Measure.map (fun u => (run k w address u).value) (unitUniform : Measure ℝ) =
      (probabilityMixture w (fun i => RealThresholdChoice.pointLaw i) hw hs : Measure (Fin (k + 1))) := by
  simp only [run_data]
  exact law k w hw hs

noncomputable def manyRun {r : ℕ} (w : Fin r → ℝ) (hr : 0 < r) (address : ℕ) (u : ℝ) :
    PRGRealRAMExecution.Run (Fin r) :=
  let h := Nat.sub_add_cancel hr
  let result := run (r - 1) (fun i => w (i.cast h)) address u
  ⟨result.value.cast h, result.trace⟩

theorem manyRun_measurable {r : ℕ} (w : Fin r → ℝ) (hr : 0 < r) (address : ℕ) :
    Measurable (fun u => (manyRun w hr address u).value) := by
  let h := Nat.sub_add_cancel hr
  change Measurable (fun u => (run (r - 1) (fun i => w (i.cast h)) address u).value.cast h)
  simp only [run_data]
  exact (measurable_of_countable (Fin.cast h)).comp (measurable_select _ _)

theorem manyRun_cost {r : ℕ} (w : Fin r → ℝ) (hr : 0 < r) (address : ℕ) (u : ℝ) :
    (manyRun w hr address u).cost ≤ 5 * r + 1 := by
  have h := run_cost (r - 1) (fun i => w (i.cast (Nat.sub_add_cancel hr))) address u
  exact h.trans (by omega)

theorem manyRun_singleton {r : ℕ} (w : Fin r → ℝ) (hr : 0 < r)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (address : ℕ) (i : Fin r) :
    Measure.map (fun u => (manyRun w hr address u).value) (unitUniform : Measure ℝ) {i} = ENNReal.ofReal (w i) := by
  let h := Nat.sub_add_cancel hr
  let w' : Fin (r - 1 + 1) → ℝ := fun a => w (a.cast h)
  have hm : ∑ a, w' a = 1 := (Equiv.sum_comp (finCongr h) w).trans hs
  have hf : (fun u => (manyRun w hr address u).value) ⁻¹' {i} = select (r - 1) w' ⁻¹' {i.cast h.symm} := by
    ext u
    change (run (r - 1) w' address u).value.cast h = i ↔ _
    rw [run_data]
    change (select (r - 1) w' u).cast h = i ↔ select (r - 1) w' u = i.cast h.symm
    constructor
    · intro hh
      apply Fin.ext
      exact congrArg (fun j : Fin r => j.val) hh
    · intro hh
      apply Fin.ext
      exact congrArg (fun j : Fin (r - 1 + 1) => j.val) hh
  rw [Measure.map_apply (manyRun_measurable w hr address) (measurableSet_singleton i), hf]
  rw [← Measure.map_apply (measurable_select _ _) (measurableSet_singleton (i.cast h.symm)),
    singleton_mass _ w' (fun a => hw (a.cast h)) hm]
  congr 1

theorem manyRun_law {r : ℕ} (w : Fin r → ℝ) (hr : 0 < r)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (address : ℕ) :
    Measure.map (fun u => (manyRun w hr address u).value) (unitUniform : Measure ℝ) =
      (probabilityMixture w (fun i => RealThresholdChoice.pointLaw i) hw hs : Measure (Fin r)) := by
  apply Measure.ext_of_singleton
  intro i
  rw [manyRun_singleton w hr hw hs address i]
  simp [probabilityMixture, mixtureMeasure, RealThresholdChoice.pointLaw, Pi.single_apply]

noncomputable def sizedRun {r : ℕ} (size : ℕ) (hSize : size = r)
    (w : Fin r → ℝ) (hr : 0 < r) (address : ℕ) (u : ℝ) : PRGRealRAMExecution.Run (Fin r) :=
  let actual := manyRun (fun i : Fin size => w (i.cast hSize)) (by omega) address u
  ⟨actual.value.cast hSize, actual.trace⟩

theorem sizedRun_eq {r : ℕ} (size : ℕ) (hSize : size = r)
    (w : Fin r → ℝ) (hr : 0 < r) (address : ℕ) (u : ℝ) :
    sizedRun size hSize w hr address u = manyRun w hr address u := by
  cases hSize
  rfl

end Blotto.GeneralPaperRealCumulativeChoice
