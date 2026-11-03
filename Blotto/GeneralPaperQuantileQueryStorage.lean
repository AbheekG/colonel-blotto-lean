import Blotto.GeneralPaperQuantilePathStorage
import Blotto.GeneralPaperActualQuantileSearch

/-! Whole root quantile-query storage. The native fresh record, descent
frames, final path fold and returned search record coexist in this
conservative reservation. As in the streaming CF ledger, primitive scratch
uses the complete bit-operation allowance; no trace or census is executed.
The reference word W is still explicit. -/
namespace Blotto.GeneralPaperQuantileQueryStorage
open GeneralPaperDyadicFloat GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery GeneralPaperMassApproximation
open GeneralPaperSourcePreparationSizes
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def outputBits (W : ℕ) (r : GeneralPaperQuantileSearch.Output) : ℕ :=
  (1+binaryWordWidth r.location)+(1+binaryWordWidth r.work)+(1+binaryWordWidth r.visits)+64*W

theorem native_metadata (m lambda k Qv digits j height : ℕ) (node : Node height)
    (hd : digits=GeneralPaperQuantileComparison.width lambda k) (hh : height≤lambda+1) :
    let found := GeneralPaperQuantileSearch.search (GeneralPaperPreparedPowers.prepare lambda k) digits j
      (GeneralPaperSourceParameters.prepare k).summarySize height node
    found.work≤GeneralPaperQuantileSearchControls.cap m lambda k Qv ∧ found.visits=height+1 := by
  have h := GeneralPaperQuantileWork.search_work lambda k digits j (GeneralPaperSourceParameters.prepare k).summarySize height node
  have hp := GeneralPaperQuantileDescentControls.step_price m lambda k Qv
  rw [←hd] at hp
  have hmass : GeneralPaperQuantileWork.massPrice lambda k≤GeneralPaperQuantileWork.stepPrice lambda k digits := by
    unfold GeneralPaperQuantileWork.stepPrice; omega
  have hprod := Nat.mul_le_mul hh hp
  dsimp only
  constructor
  · unfold GeneralPaperQuantileSearchControls.cap GeneralPaperQuantileDescentControls.cap
    nlinarith only [h,hprod,hmass,hp,hh,Nat.zero_le (1048576*(measure m lambda k Qv+1)^2)]
  · exact GeneralPaperQuantileDescent.visits _ _ _ _ _ _ _ _ _ _

theorem output_bound (W m lambda k Qv digits j height : ℕ) (node : Node height)
    (hd : digits=GeneralPaperQuantileComparison.width lambda k) (hh : height≤lambda+1) :
    outputBits W (GeneralPaperQuantileSearch.search (GeneralPaperPreparedPowers.prepare lambda k) digits j
      (GeneralPaperSourceParameters.prepare k).summarySize height node)≤
      height+2+8*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+64*W := by
  let p := GeneralPaperPreparedPowers.prepare lambda k
  let d := GeneralPaperQuantileDescent.run p digits j (GeneralPaperSourceParameters.prepare k).summarySize
    (fresh p 0 node).number height node 0 (fresh p 0 node).number zero
  have hm := native_metadata m lambda k Qv digits j height node hd hh
  have hw := binaryWordWidth_mono hm.1
  have hc := GeneralPaperQuantileSearchControls.cap_word m lambda k Qv
  have hhW := GeneralPaperQuantileDescentControls.height_word m lambda k Qv
  have hvW := binaryWordWidth_mono (show height+1≤lambda+2 by omega)
  have hcode := GeneralPaperQuantilePathStorage.output d.path
  have hlen : d.path.length=height := GeneralPaperQuantileDescent.path_length ..
  rw [hlen] at hcode
  unfold outputBits
  change (1+binaryWordWidth (GeneralPaperQuantilePath.encode d.path))+_+_+64*W≤_
  rw [hm.2]
  omega

def window (model : RationalCostModel) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (digits j height : ℕ) (node : Node height) : ℕ :=
  let p := c.powers
  let s := c.controls.source.summarySize
  let t := fresh p 0 node
  let d := GeneralPaperQuantileDescent.run p digits j s t.number height node 0 t.number zero
  GeneralPaperQuantileTraversalStorage.peak W p digits j s t.number height node 0 t.number zero+
    GeneralPaperQuantilePathStorage.peak W d.path 0+
    outputBits W (GeneralPaperQuantileSearch.search p digits j s height node)+
    GeneralPaperStoredNumberBits.bits t.number+(1+binaryWordWidth t.work)+512*W+
    (GeneralPaperQuantileSearchExecution.run true model.rat W c digits j height node).2

def profile (model : RationalCostModel) (W m lambda k Qv height : ℕ) : ℕ :=
  (height+1)^2*GeneralPaperQuantileTraversalStorage.coefficient W m lambda k Qv+
    (height+1)*(3*(height+3)+256*W)+height+2+
    10*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+576*W+
    GeneralPaperQuantileSearchPrice.profile model.rat W m lambda k Qv height

theorem bounded (model : RationalCostModel) (W m lambda k Qv digits j height : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (node : Node height) (hd : digits=GeneralPaperQuantileComparison.width lambda k)
    (hj : j≤(GeneralPaperSourceParameters.prepare k).summarySize) (hh : height≤lambda+1)
    (hv : Valid lambda k node) (hp : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node) :
    window model W c digits j height node≤profile model W m lambda k Qv height := by
  have hScratch := GeneralPaperQuantileSearchPrice.bit_work model.rat model.monotone W m lambda k Qv digits j height
    c hc hd node hj hh hv hp
  subst c
  let p := GeneralPaperPreparedPowers.prepare lambda k
  let d := GeneralPaperQuantileDescent.run p digits j (GeneralPaperSourceParameters.prepare k).summarySize
    (fresh p 0 node).number height node 0 (fresh p 0 node).number zero
  have hDescent := GeneralPaperQuantileTraversalStorage.root W m lambda k Qv digits j height node hd hj hh hv hp
  have hPath := GeneralPaperQuantilePathStorage.bounded W d.path
  have hlen : d.path.length=height := GeneralPaperQuantileDescent.path_length ..
  rw [hlen] at hPath
  have hOut := output_bound W m lambda k Qv digits j height node hd hh
  have hFresh := fresh_bound lambda k 0 node hh hv hp
  have hSafe := GeneralPaperQuantileExponentRange.initial lambda k digits j
    (GeneralPaperSourceParameters.prepare k).summarySize height node hh hv hp
  have hState : GeneralPaperQuantileExponentRange.StateBound (GeneralPaperQuantileExponentRange.cap lambda k)
      (fresh p 0 node).number (fresh p 0 node).number zero := by
    cases height with
    | zero => exact hSafe
    | succ height => exact hSafe.1
  have hNumber := GeneralPaperStoredNumberBits.operand m lambda k Qv (fresh p 0 node).number hFresh.1 hState.1
  have hWork : 1+binaryWordWidth (fresh p 0 node).work≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
    have hm := fresh_work lambda k 0 node
    change (fresh p 0 node).work≤GeneralPaperQuantileWork.massPrice lambda k at hm
    have hmass : GeneralPaperQuantileWork.massPrice lambda k≤GeneralPaperQuantileWork.stepPrice lambda k digits := by
      unfold GeneralPaperQuantileWork.stepPrice; omega
    have hs := GeneralPaperQuantileDescentControls.step_price m lambda k Qv
    rw [←hd] at hs
    have hcap : (fresh p 0 node).work≤GeneralPaperQuantileDescentControls.cap m lambda k Qv := by
      unfold GeneralPaperQuantileDescentControls.cap
      nlinarith only [hm,hmass,hs,Nat.zero_le ((lambda+1)*(1048576*(measure m lambda k Qv+1)^2))]
    have hw := binaryWordWidth_mono hcap
    have hcW := GeneralPaperQuantileDescentControls.cap_word m lambda k Qv
    omega
  have hSum := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hDescent hPath) hOut) hNumber) hWork)
    (Nat.le_refl (512*W))
  exact (Nat.add_le_add hSum hScratch).trans_eq (by unfold profile; ring)

end Blotto.GeneralPaperQuantileQueryStorage
