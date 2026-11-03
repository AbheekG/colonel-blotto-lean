import Blotto.GeneralPaperCatalogueEpochFeasible

/-! Actual epoch choices and every recorded pre-update candidate decode to
canonical real allocations with hard at-most budgets. These are finite-epoch
output invariants, not continuous security or a full source guarantee.
-/
namespace Blotto.GeneralPaperCatalogueEpochOutput
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRows GeneralPaperCatalogueEpoch
open GeneralPaperCatalogueRowSemantics
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 2048

theorem rational_feasible {m : ℕ} (B : ℚ) (allocation : Fin m → ℚ)
    (hNonneg : ∀ j, 0≤allocation j) (hBudget : (∑ j, allocation j)≤B) :
    Feasible (B:ℝ) (fun j => (allocation j:ℝ)) := by
  constructor
  · intro j
    change (0:ℝ)≤(allocation j:ℝ)
    exact_mod_cast hNonneg j
  · change (∑ j, (allocation j:ℝ))≤(B:ℝ)
    exact_mod_cast hBudget

theorem round_candidate_decoded {m k : ℕ} (cache : Cache m k) (powers : GeneralPaperPreparedPowers.Prepared)
    (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (state : State cache) :
    let rows := chooseRows cache profit T weights (GeneralPaperAdaptiveEpoch.snapshots powers state.fields) Bc Br
    ∀ j, (decode cache.alphabet false ((round cache powers profit T weights Bc Br state).candidate.read j)).choice=
      some ((rowChoices cache.candidate.data rows.candidate).read j) := by
  dsimp only
  intro j
  have he := GeneralPaperCatalogueOptimizerBudget.output_decoded cache.candidate
    (chooseRows cache profit T weights (GeneralPaperAdaptiveEpoch.snapshots powers state.fields) Bc Br).candidate j
  have ha : cache.candidate.alphabet=cache.alphabet := by rw [cache.candidate_spec]; rfl
  have hr : cache.candidate.response=false := by rw [cache.candidate_spec]; rfl
  rw [ha,hr] at he
  exact he

theorem round_response_decoded {m k : ℕ} (cache : Cache m k) (powers : GeneralPaperPreparedPowers.Prepared)
    (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (state : State cache) :
    let rows := chooseRows cache profit T weights (GeneralPaperAdaptiveEpoch.snapshots powers state.fields) Bc Br
    ∀ j, (decode cache.alphabet true ((round cache powers profit T weights Bc Br state).response.read j)).choice=
      some ((rowChoices cache.response.data rows.response).read j) := by
  dsimp only
  intro j
  have he := GeneralPaperCatalogueOptimizerBudget.output_decoded cache.response
    (chooseRows cache profit T weights (GeneralPaperAdaptiveEpoch.snapshots powers state.fields) Bc Br).response j
  have ha : cache.response.alphabet=cache.alphabet := by rw [cache.response_spec]; rfl
  have hr : cache.response.response=true := by rw [cache.response_spec]; rfl
  rw [ha,hr] at he
  exact he

theorem executed_candidate_feasible {m k : ℕ} (cache : Cache m k) (Qv q qbar : ℕ) (hm : 0<m) (hQv : 0<Qv) (hq : 0<q)
    (hCap : q≤qbar) (weights : FixedArrayTable m ℕ) (hWeights : ∑ j, weights.read j=Qv)
    (Bc Br : ℚ) (hB : 0≤Bc) (hBudgetDen : Bc.den∣q) (time : ℕ)
    (hTime : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) :
    let profit := GeneralPaperProfitParameters.prepare m cache.alphabet.lambda k Qv
    let T := (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).rows
    let powers := GeneralPaperPreparedPowers.prepare cache.alphabet.lambda k
    let state := (execute cache powers profit T weights Bc Br (initial cache) time).1
    let rows := chooseRows cache profit T weights (GeneralPaperAdaptiveEpoch.snapshots powers state.fields) Bc Br
    Feasible (Bc:ℝ) (fun j => (((rowChoices cache.candidate.data rows.candidate).read j).physical
      (GeneralPaperTagBudgetTransfer.shift m qbar cache.alphabet.C):ℝ)) := by
  dsimp only
  let profit := GeneralPaperProfitParameters.prepare m cache.alphabet.lambda k Qv
  let T := (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).rows
  let powers := GeneralPaperPreparedPowers.prepare cache.alphabet.lambda k
  let state := (execute cache powers profit T weights Bc Br (initial cache) time).1
  let before := GeneralPaperAdaptiveEpoch.snapshots powers state.fields
  obtain ⟨hn,hb⟩ := GeneralPaperCatalogueEpochFeasible.candidate_feasible cache Qv q qbar hm hQv hq hCap weights hWeights before
    (fun j => GeneralPaperCatalogueEpochBounds.snapshots_positive cache profit T weights Bc Br time hTime j)
    (GeneralPaperCatalogueEpochBounds.snapshots_coherent cache powers state) Bc Br hB hBudgetDen
  exact rational_feasible Bc _ hn hb

theorem executed_response_feasible {m k : ℕ} (cache : Cache m k) (Qv q qbar : ℕ) (hm : 0<m) (hQv : 0<Qv) (hq : 0<q)
    (hCap : q≤qbar) (weights : FixedArrayTable m ℕ) (hWeights : ∑ j, weights.read j=Qv)
    (Bc Br : ℚ) (hB : 0≤Br) (hBudgetDen : Br.den∣q) (time : ℕ)
    (hTime : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) :
    let profit := GeneralPaperProfitParameters.prepare m cache.alphabet.lambda k Qv
    let T := (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).rows
    let powers := GeneralPaperPreparedPowers.prepare cache.alphabet.lambda k
    let state := (execute cache powers profit T weights Bc Br (initial cache) time).1
    let rows := chooseRows cache profit T weights (GeneralPaperAdaptiveEpoch.snapshots powers state.fields) Bc Br
    Feasible (Br:ℝ) (fun j => (((rowChoices cache.response.data rows.response).read j).physical
      (GeneralPaperTagBudgetTransfer.shift m qbar cache.alphabet.C):ℝ)) := by
  dsimp only
  let profit := GeneralPaperProfitParameters.prepare m cache.alphabet.lambda k Qv
  let T := (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).rows
  let powers := GeneralPaperPreparedPowers.prepare cache.alphabet.lambda k
  let state := (execute cache powers profit T weights Bc Br (initial cache) time).1
  let before := GeneralPaperAdaptiveEpoch.snapshots powers state.fields
  obtain ⟨hn,hb⟩ := GeneralPaperCatalogueEpochFeasible.response_feasible cache Qv q qbar hm hQv hq hCap weights hWeights before
    (fun j => GeneralPaperCatalogueEpochBounds.snapshots_positive cache profit T weights Bc Br time hTime j)
    (GeneralPaperCatalogueEpochBounds.snapshots_coherent cache powers state) Bc Br hB hBudgetDen
  exact rational_feasible Br _ hn hb

theorem recorded_candidate_feasible {m k : ℕ} (cache : Cache m k) (Qv q qbar : ℕ) (hm : 0<m) (hQv : 0<Qv) (hq : 0<q)
    (hCap : q≤qbar) (weights : FixedArrayTable m ℕ) (hWeights : ∑ j, weights.read j=Qv)
    (Bc Br : ℚ) (hB : 0≤Bc) (hBudgetDen : Bc.den∣q) (count time : ℕ)
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) (hTime : time<count) :
    let profit := GeneralPaperProfitParameters.prepare m cache.alphabet.lambda k Qv
    let T := (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).rows
    let powers := GeneralPaperPreparedPowers.prepare cache.alphabet.lambda k
    let trajectory := (execute cache powers profit T weights Bc Br (initial cache) count).2
    ∃ choices : FixedArrayTable m Choice,
      (∀ j, (decode cache.alphabet false ((trajectory[time]'(by rw [trajectory_size]; exact hTime)).read j)).choice=some (choices.read j)) ∧
      Feasible (Bc:ℝ) (fun j => ((choices.read j).physical (GeneralPaperTagBudgetTransfer.shift m qbar cache.alphabet.C):ℝ)) := by
  dsimp only
  let profit := GeneralPaperProfitParameters.prepare m cache.alphabet.lambda k Qv
  let T := (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).rows
  let powers := GeneralPaperPreparedPowers.prepare cache.alphabet.lambda k
  let state := (execute cache powers profit T weights Bc Br (initial cache) time).1
  let rows := chooseRows cache profit T weights (GeneralPaperAdaptiveEpoch.snapshots powers state.fields) Bc Br
  refine ⟨rowChoices cache.candidate.data rows.candidate,?_,?_⟩
  · intro j
    rw [trajectory_read cache powers profit T weights Bc Br (initial cache) count time hTime]
    exact round_candidate_decoded cache powers profit T weights Bc Br state j
  · exact executed_candidate_feasible cache Qv q qbar hm hQv hq hCap weights hWeights Bc Br hB hBudgetDen time (by omega)

end Blotto.GeneralPaperCatalogueEpochOutput
