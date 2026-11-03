import Blotto.GeneralPaperEqualRealDispatch

/-! One branch-dependent draw from the actual equal-budget return. A pure
row is copied from stored cells; the grouped branch uses its smaller cache.
Independent whole seeds map to the product of the actual output laws. -/
namespace Blotto.GeneralPaperEqualRealBranchDraw
open MeasureTheory PRGRealRAMExecution
open GeneralPaperEqualRealBranch (Prepared outputLaw)
set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable def copyRow {n : ℕ} (row : RationalResourceArray n) : Run (FixedArrayTable n ℝ) :=
  GeneralPaperEqualRealEmission.arrayRunSized row.data.size row.size
    (fun j => ⟨(row.allocation j : ℝ), [.load j.val (row.allocation j : ℝ)]⟩)

theorem copy_data {n : ℕ} (row : RationalResourceArray n) : (copyRow row).value.read = row.realAllocation := by
  funext j
  rw [copyRow, GeneralPaperEqualRealEmission.arrayRunSized_eq, arrayRun_read]
  rfl

theorem copy_work {n : ℕ} (row : RationalResourceArray n) : (copyRow row).cost = 3 * n + 2 := by
  rw [copyRow, GeneralPaperEqualRealEmission.arrayRunSized_eq, arrayRun_cost]
  simp [Run.cost, Operation.cost, Nat.mul_comm, Nat.add_comm]

noncomputable def grouped {n m r K : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (cache : GeneralPaperEqualRealCache.Cache G l) (hK : cache.midpointBits = K)
    (u : ℝ) (fresh : Fin K → Bool) : GeneralPaperEqualRealDraw.Result n :=
  GeneralPaperEqualRealCacheDraw.run cache u (fun j => fresh (j.cast hK))

noncomputable def seedLaw (K : ℕ) : ProbabilityMeasure (ℝ × (Fin K → Bool)) :=
  ⟨(unitUniform : Measure ℝ).prod (fairBitLaw K : Measure (Fin K → Bool)), inferInstance⟩

theorem grouped_measurable {n m r K : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (cache : GeneralPaperEqualRealCache.Cache G l) (hK : cache.midpointBits = K) :
    Measurable (fun z : ℝ × (Fin K → Bool) => (grouped cache hK z.1 z.2).output.read) := by
  subst K
  exact GeneralPaperEqualRealCacheDraw.measurable_run cache

theorem grouped_law {n m r K : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (cache : GeneralPaperEqualRealCache.Cache G l) (hK : cache.midpointBits = K) :
    (seedLaw K).map (fun z => (grouped cache hK z.1 z.2).output.read) = GeneralPaperEqualRealCacheDraw.outputLaw cache := by
  subst K
  rfl

noncomputable def run {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (p : Prepared v k budget) (u : ℝ) (fresh : Fin (k + 5) → Bool) : GeneralPaperEqualRealDraw.Result n :=
  match p with
  | .dominant _ _ row _ =>
    let copied := copyRow row
    ⟨copied.value, 0, 0, copied.cost + 8⟩
  | .grouped _ cache hK _ => grouped cache hK u fresh

theorem measurable_run {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : Prepared v k budget) :
    Measurable (fun z : ℝ × (Fin (k + 5) → Bool) => (run p z.1 z.2).output.read) := by
  cases p with
  | dominant chosen heavy row correct =>
    change Measurable (fun _ : ℝ × (Fin (k + 5) → Bool) => (copyRow row).value.read)
    exact measurable_const
  | grouped small cache hK hB => exact grouped_measurable cache hK

theorem law {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : Prepared v k budget) :
    (seedLaw (k + 5)).map (fun z => (run p z.1 z.2).output.read) = outputLaw p := by
  cases p with
  | dominant chosen heavy row correct =>
    apply ProbabilityMeasure.toMeasure_injective
    change Measure.map (fun _ : ℝ × (Fin (k + 5) → Bool) => (copyRow row).value.read)
      (seedLaw (k + 5) : Measure _) = Measure.dirac row.realAllocation
    rw [copy_data, Measure.map_const, measure_univ, one_smul]
  | grouped small cache hK hB => exact grouped_law cache hK

theorem independent_players {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : Prepared v k budget) :
    let μ := (seedLaw (k + 5) : Measure (ℝ × (Fin (k + 5) → Bool)))
    let f := fun z : ℝ × (Fin (k + 5) → Bool) => (run p z.1 z.2).output.read
    Measure.map (Prod.map f f) (μ.prod μ) = (outputLaw p : Measure (Allocation n)).prod (outputLaw p : Measure (Allocation n)) := by
  dsimp only
  rw [← law p]
  exact (Measure.map_prod_map _ _ (measurable_run p) (measurable_run p)).symm

theorem work {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (p : Prepared v k budget) (u : ℝ) (fresh : Fin (k + 5) → Bool) :
    (run p u fresh).work ≤ 1024 * (n + k + 1) := by
  cases p with
  | dominant chosen heavy row correct =>
    simp only [run, copy_work]
    omega
  | grouped small cache hK hB =>
    have h := GeneralPaperEqualRealCacheDraw.work cache u (fun j => fresh (j.cast hK))
    have hm := GeneralPaperEqualNativeCache.group_count v small
    have hr := (GeneralPaperEqualNativeCache.compact_count v small).2
    have hn := v.fields_positive
    change (GeneralPaperEqualRealCacheDraw.run cache u _).work ≤ _
    omega

theorem reads {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (p : Prepared v k budget) (u : ℝ) (fresh : Fin (k + 5) → Bool) :
    (run p u fresh).uniformReads ≤ 1 ∧ (run p u fresh).bitReads ≤ k + 5 := by
  cases p with
  | dominant chosen heavy row correct =>
    change 0 ≤ 1 ∧ 0 ≤ k + 5
    omega
  | grouped small cache hK hB =>
    have h := GeneralPaperEqualRealCacheDraw.reads cache u (fun j => fresh (j.cast hK))
    change (GeneralPaperEqualRealCacheDraw.run cache u _).uniformReads ≤ 1 ∧
      (GeneralPaperEqualRealCacheDraw.run cache u _).bitReads ≤ k + 5
    rw [h.1, h.2, hK]
    exact ⟨le_rfl, le_rfl⟩

theorem grouped_budget {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1)
    (cache : GeneralPaperEqualRealCache.Cache (GeneralPaperEqualFiniteKernel.terminal v small).partition
      (GeneralPaperEqualFiniteKernel.lottery v small))
    (hB : 0 ≤ cache.budget) (u : ℝ) (fresh : Fin cache.midpointBits → Bool) :
    FullBudget (cache.budget : ℝ) (GeneralPaperEqualRealCacheDraw.run cache u fresh).output.read := by
  let p := GeneralPaperEqualRealCache.view cache
  let slot := (GeneralPaperEqualRealDraw.choose p u).value
  have h := GeneralPaperEqualCachedEmission.emit_fullBudget p RationalCostModel.schoolbook (fun _ => 1) 1 hB
    (GeneralPaperEqualFiniteKernel.endpoints v small) slot fresh
  have he := (GeneralPaperEqualRealDraw.data p u fresh).trans
    (GeneralPaperEqualRealDraw.point_eq_emit p RationalCostModel.schoolbook (fun _ => 1) 1 slot fresh)
  exact he.symm ▸ h

theorem hard_budget {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (p : Prepared v k budget) (hB : 0 ≤ budget) (u : ℝ) (fresh : Fin (k + 5) → Bool) :
    FullBudget (budget : ℝ) (run p u fresh).output.read := by
  cases p with
  | dominant chosen heavy row correct =>
    simp only [run, copy_data, correct]
    exact PureBoundaryEquilibria.vertex_fullBudget _ (by exact_mod_cast hB) chosen
  | grouped small cache hK hBudget =>
    have hc : 0 ≤ cache.budget := by rw [hBudget]; exact hB
    have h := grouped_budget v small cache hc u (fun j => fresh (j.cast hK))
    simpa only [run, grouped, hBudget] using h

end Blotto.GeneralPaperEqualRealBranchDraw
