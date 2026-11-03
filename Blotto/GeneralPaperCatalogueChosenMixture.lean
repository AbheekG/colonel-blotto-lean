import Blotto.GeneralPaperCatalogueGameGap

/-! The actual chosen whole rows form feasible finite comparator laws.
Both empirical laws use one shared uniform time label per whole allocation.
The candidate law agrees with the already-returned T-row source table.
-/
namespace Blotto.GeneralPaperCatalogueChosenMixture
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperCodeMixture GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
open GeneralPaperCatalogueFiniteFamilies GeneralPaperCatalogueRowSemantics
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

def choices {m : ℕ} (response : Bool) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) : FixedArrayTable m Choice :=
  let c := cacheAt (prepare a k Qv weights Bc Br) a k (time/(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
  let run := GeneralPaperCatalogueEpochRun.selected c Qv weights Bc Br
  let rows := GeneralPaperCatalogueEpochRun.rowsAt run (time%(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
  if response then rowChoices c.response.data rows.response else rowChoices c.candidate.data rows.candidate

theorem chosen_decoded {m : ℕ} (response : Bool) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (time : ℕ) (j : Fin m) :
    (GeneralPaperCodeDecode.decode a response (row response a k Qv weights Bc Br time j).val).choice=
      some ((choices response a k Qv weights Bc Br time).read j) := by
  let c := cacheAt (prepare a k Qv weights Bc Br) a k (time/(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
  let run := GeneralPaperCatalogueEpochRun.selected c Qv weights Bc Br
  let rows := GeneralPaperCatalogueEpochRun.rowsAt run (time%(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
  cases response with
  | false =>
    have he := GeneralPaperCatalogueOptimizerBudget.output_decoded c.candidate rows.candidate j
    have ha : c.candidate.alphabet=a := by rw [c.candidate_spec]; rfl
    have hr : c.candidate.response=false := by rw [c.candidate_spec]; rfl
    rw [ha,hr] at he
    exact he
  | true =>
    have he := GeneralPaperCatalogueOptimizerBudget.output_decoded c.response rows.response j
    have ha : c.response.alphabet=a := by rw [c.response_spec]; rfl
    have hr : c.response.response=true := by rw [c.response_spec]; rfl
    rw [ha,hr] at he
    exact he

theorem chosen_tag_budget {m : ℕ} (response : Bool) (a : Alphabet) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hWeights : ∑ j, weights.read j=Qv) (Bc Br : ℚ) (hB : 0≤(if response then Br else Bc))
    (time : ℕ) (ht : time<(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) :
    (∑ j, ((choices response a k Qv weights Bc Br time).read j).tag)≤
      GeneralPaperResponseTag.budget (if response then Br else Bc) := by
  let c := cacheAt (prepare a k Qv weights Bc Br) a k (time/(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
  let run := GeneralPaperCatalogueEpochRun.selected c Qv weights Bc Br
  let localTime := time%(GeneralPaperTrajectoryParameters.prepare a.lambda k).period
  let before := GeneralPaperCatalogueEpochRun.beforeAt run localTime
  let rows := GeneralPaperCatalogueEpochRun.rowsAt run localTime
  have hLocal : localTime≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period :=
    (Nat.mod_lt time (GeneralPaperCatalogueGlobalHistory.period_positive a.lambda k)).le
  have hp : ∀ j, GeneralPaperEpochSnapshot.Positive (before.read j) :=
    GeneralPaperCatalogueEpochRun.selected_positive c Qv weights Bc Br localTime hLocal
  have hc : ∀ j, GeneralPaperEpochSnapshot.Coherent (before.read j) :=
    GeneralPaperCatalogueEpochRun.snapshot_coherent run localTime
  cases response with
  | false =>
    have hf := GeneralPaperCatalogueEpochFeasible.candidate_feasible c Qv Bc.den Bc.den hm hQv (Rat.den_pos Bc) le_rfl weights hWeights
      before hp hc Bc Br hB (dvd_refl _)
    have he := (GeneralPaperCatalogueOptimizerBudget.output_budget_iff c.candidate Bc.den Bc.den hm (Rat.den_pos Bc) le_rfl Bc
      (dvd_refl _) rows.candidate).mp hf.2
    exact he
  | true =>
    have hf := GeneralPaperCatalogueEpochFeasible.response_feasible c Qv Br.den Br.den hm hQv (Rat.den_pos Br) le_rfl weights hWeights
      before hp hc Bc Br hB (dvd_refl _)
    have he := (GeneralPaperCatalogueOptimizerBudget.output_budget_iff c.response Br.den Br.den hm (Rat.den_pos Br) le_rfl Br
      (dvd_refl _) rows.response).mp hf.2
    exact he

noncomputable def empirical {m : ℕ} (response : Bool) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    Mixture m (2^a.lambda) where
  labels := (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows
  weight := fun _ => 1/((GeneralPaperTrajectoryParameters.prepare a.lambda k).rows:ℝ)
  rows := fun t j => row response a k Qv weights Bc Br t.val j
  nonnegative := by intro t; positivity
  total := by
    have ht : (0:ℝ)<(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows :=
      by exact_mod_cast GeneralPaperTrajectoryParameters.rows_positive a.lambda k
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp

theorem empirical_marginal {m : ℕ} (response : Bool) (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (j : Fin m) :
    GeneralPaperCodeMixture.marginal (empirical response a k Qv weights Bc Br) j=
      GeneralPaperCodeAverages.empirical (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows
        (fun t => row response a k Qv weights Bc Br t j) := by
  funext i
  unfold GeneralPaperCodeMixture.marginal empirical GeneralPaperCodeAverages.empirical GeneralPaperCodeAverages.mean
  simp only [one_div_mul_eq_div,← Finset.sum_div]
  exact congrArg (fun value : ℝ => value/((GeneralPaperTrajectoryParameters.prepare a.lambda k).rows:ℝ))
    (Fin.sum_univ_eq_sum_range (fun t => GeneralPaperCodeAverages.point (row response a k Qv weights Bc Br t j) i) _)

noncomputable def feasible_empirical {m : ℕ} (response : Bool) (a : Alphabet) (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hWeights : ∑ j, weights.read j=Qv) (Bc Br : ℚ) (hB : 0≤(if response then Br else Bc)) :
    GeneralPaperCatalogueMixtureOptimizer.Feasible (m:=m) a response (if response then Br else Bc) where
  law := empirical response a k Qv weights Bc Br
  choices := fun t => choices response a k Qv weights Bc Br t.val
  decoded := fun t j => chosen_decoded response a k Qv weights Bc Br t.val j
  budget := fun t => chosen_tag_budget response a k Qv hm hQv weights hWeights Bc Br hB t.val t.isLt

theorem candidate_table_code {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (t : Fin (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows) (j : Fin m) :
    ((empirical false a k Qv weights Bc Br).rows t j).val=
      ((GeneralPaperCatalogueFullTrajectory.table a k Qv weights Bc Br).read t).read j := by
  rw [GeneralPaperCatalogueFullTrajectory.read_preupdate]
  rfl

end Blotto.GeneralPaperCatalogueChosenMixture
