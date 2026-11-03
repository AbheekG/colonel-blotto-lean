import Blotto.GeneralPaperPhysicalResponseExecution

/-! Extend one existing native round with the required physical response
check. Consume its returned response array directly, without selector or
snapshot replay. The rational temporary row is released after its check. -/
namespace Blotto.GeneralPaperPhysicalResponseRound
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRows GeneralPaperCatalogueEpoch
open GeneralPaperCatalogueRowSemantics GeneralPaperCodeAlphabet
open GeneralPaperUnsignedCellConstancy (Prefix)
open GeneralPaperSourceRowsExecution GeneralPaperSummaryArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 8192

def run {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (cache : Cache m k)
    (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ)
    (Bc Br delta : ℚ) (state : State cache) : (RoundResult cache × Bool) × ℕ :=
  let selected := GeneralPaperRoundExecution.run bits index price W c cache profit T weights Bc Br state
  let checked := GeneralPaperPhysicalResponseExecution.run bits model W cache.alphabet delta selected.1.response Br
  ((selected.1,checked.1.2),selected.2+checked.2+128*W)

theorem base_data {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (cache : Cache m k)
    (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ)
    (Bc Br delta : ℚ) (state : State cache) : (run bits index price model W c cache profit T weights Bc Br delta state).1.1=
      (GeneralPaperRoundExecution.run bits index price W c cache profit T weights Bc Br state).1 := rfl

theorem data {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (model : RationalCostModel) (W lambda Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ)
    (weights : FixedArrayTable m ℕ) (Bc Br delta : ℚ) (state : State cache)
    (hSpan : profit.parameters.leafCount=2^profit.parameters.height) :
    (run bits index price model W c cache profit T weights Bc Br delta state).1.1=
      round cache c.powers profit T weights Bc Br state :=
  GeneralPaperRoundExecution.data bits index price W lambda Qv c hc cache profit T weights Bc Br state hSpan

theorem decoded_response {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W lambda Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (state : State cache)
    (hSpan : profit.parameters.leafCount=2^profit.parameters.height) (j : Fin m) :
    GeneralPaperPhysicalBidExecution.decodedChoice cache.alphabet
      ((GeneralPaperRoundExecution.run bits index price W c cache profit T weights Bc Br state).1.response.read j)=
      (rowChoices cache.response.data (chooseRows cache profit T weights
        (GeneralPaperAdaptiveEpoch.snapshots c.powers state.fields) Bc Br).response).read j := by
  apply GeneralPaperPhysicalBidExecution.decoded_choice_of_some
  rw [GeneralPaperRoundExecution.data bits index price W lambda Qv c hc cache profit T weights Bc Br state hSpan]
  exact GeneralPaperCatalogueEpochOutput.round_response_decoded cache c.powers profit T weights Bc Br state j

theorem response_code_bound {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W lambda Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (state : State cache)
    (hSpan : profit.parameters.leafCount=2^profit.parameters.height) (j : Fin m) :
    ((GeneralPaperRoundExecution.run bits index price W c cache profit T weights Bc Br state).1.response.read j)≤8*cache.alphabet.C := by
  have hd := GeneralPaperCatalogueEpochOutput.round_response_decoded cache c.powers profit T weights Bc Br state j
  have hv := GeneralPaperCodeDecodeSound.decode_valid cache.alphabet true _ _ hd
  have hb := (valid_in_alphabet cache.alphabet true _ hv).le
  rw [GeneralPaperRoundExecution.data bits index price W lambda Qv c hc cache profit T weights Bc Br state hSpan]
  exact hb

theorem bit_overhead {m k : ℕ} (model : RationalCostModel) (W lambda Qv qbar t : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ)
    (weights : FixedArrayTable m ℕ) (Bc Br delta : ℚ) (state : State cache)
    (hSpan : profit.parameters.leafCount=2^profit.parameters.height)
    (hd : RationalHeight delta (GeneralPaperResponsePhysicalHeights.shiftHeight m qbar cache.alphabet.C))
    (hBr : RationalHeight Br t) :
    (run true (fun w => w) model.rat model W c cache profit T weights Bc Br delta state).2≤
      (GeneralPaperRoundExecution.run true (fun w => w) model.rat W c cache profit T weights Bc Br state).2+
      GeneralPaperPhysicalResponseExecution.bitProfile model W m qbar t cache.alphabet+128*W := by
  have h := GeneralPaperPhysicalResponseExecution.bit_work model W qbar t cache.alphabet delta hd _
    (response_code_bound true (fun w => w) model.rat W lambda Qv c hc cache profit T weights Bc Br state hSpan) Br hBr
  exact Nat.add_le_add_right (Nat.add_le_add_left h _) _

theorem arithmetic_overhead {m k : ℕ} (price : ℕ → ℕ) (model : RationalCostModel)
    (c : GeneralPaperMaterializedPowerCache.Cache) (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared)
    (T : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br delta : ℚ) (state : State cache) :
    (run false (fun _ => 1) price model 1 c cache profit T weights Bc Br delta state).2≤
      (GeneralPaperRoundExecution.run false (fun _ => 1) price 1 c cache profit T weights Bc Br state).2+
      GeneralPaperPhysicalResponseExecution.arithmeticProfile m cache.alphabet+128 :=
  Nat.add_le_add_right (Nat.add_le_add_left
    (GeneralPaperPhysicalResponseExecution.arithmetic_work model cache.alphabet delta _ Br) _) _

theorem checked_reached {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (model : RationalCostModel) (W Qv q qbar time : ℕ)
    (cache : Cache m k) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hm : 0<m) (hQv : 0<Qv) (hq : 0<q)
    (hCap : q≤qbar) (hw : ∑ j,weights.read j=Qv) (hB : 0≤Br) (hDen : Br.den∣q)
    (hTime : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) :
    let profit := GeneralPaperProfitParameters.prepare m cache.alphabet.lambda k Qv
    let T := (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).rows
    let powers := GeneralPaperPreparedPowers.prepare cache.alphabet.lambda k
    let state := (execute cache powers profit T weights Bc Br (initial cache) time).1
    (run bits index price model W c cache profit T weights Bc Br
      (GeneralPaperTagBudgetTransfer.shift m qbar cache.alphabet.C) state).1.2=true := by
  dsimp only
  let profit := GeneralPaperProfitParameters.prepare m cache.alphabet.lambda k Qv
  let T := (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).rows
  let powers := GeneralPaperPreparedPowers.prepare cache.alphabet.lambda k
  let state := (execute cache powers profit T weights Bc Br (initial cache) time).1
  change (run bits index price model W c cache profit T weights Bc Br
    (GeneralPaperTagBudgetTransfer.shift m qbar cache.alphabet.C) state).1.2=true
  have hSpan : profit.parameters.leafCount=2^profit.parameters.height :=
    GeneralPaperProfitParameters.leaf_count_spec m cache.alphabet.lambda k Qv
  have hp : c.powers=GeneralPaperPreparedPowers.prepare cache.alphabet.lambda k := by rw [hc]; rfl
  have hFeasible := GeneralPaperCatalogueEpochOutput.executed_response_feasible cache Qv q qbar hm hQv hq hCap
    weights hw Bc Br hB hDen time hTime
  dsimp only at hFeasible
  have hd := decoded_response bits index price W cache.alphabet.lambda Qv c hc cache profit T weights Bc Br state hSpan
  unfold run
  dsimp only
  apply GeneralPaperPhysicalResponseExecution.checks_of_physical_budget
  simp only [hd,hp]
  constructor
  · intro j
    have hj := hFeasible.1 j
    dsimp only at hj
    exact_mod_cast hj
  · have hs := hFeasible.2
    dsimp only at hs
    exact_mod_cast hs

end Blotto.GeneralPaperPhysicalResponseRound
