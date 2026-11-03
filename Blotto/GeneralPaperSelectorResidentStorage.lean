import Blotto.GeneralPaperNativeSelectorOutputStorage

/-! The reached source core coexists with native input/tree/DP and full
decode/trim/fallback output windows. Counting both sequential selectors is
conservative and covers the first returned row retained during the second.
This is an abstract phase-window join; global W, remaining construction/
scatter/root-selection/query peaks and primitive scratch remain open. -/
namespace Blotto.GeneralPaperSelectorResidentStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochRun
open GeneralPaperUnsignedCellConstancy (Prefix)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def window {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A k Qv : ℕ) (a : Alphabet)
    (shared : Shared m) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time count : ℕ) (hc : count≤m) : ℕ :=
  let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
  let cache := GeneralPaperCatalogueShared.cache shared a k trees
  let current := epochRun shared a k trees
  let before := beforeAt current time
  let cp := FixedArrayTable.ofFn (fun j => (before.read j).lambda.cdf)
  let rp := FixedArrayTable.ofFn (fun j => (before.read j).mu.cdf)
  (GeneralPaperEncodedSharedSource.footprint W shared+GeneralPaperEpochResidentStorage.footprint W k Qv a weights Bc Br epoch time)+
    GeneralPaperActualProfitTreeStorage.window W current.T current.profit cache.candidate weights cp+
    GeneralPaperActualProfitTreeStorage.window W current.T current.profit cache.response weights rp+
    GeneralPaperNativeSelectorOutputStorage.window bits index price W A current.profit current.T cache.candidate weights cp Bc count hc+
    GeneralPaperNativeSelectorOutputStorage.window bits index price W A current.profit current.T cache.response weights rp Br count hc

def profile {m : ℕ} (W k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : ℕ :=
  let prepared := GeneralPaperProfitParameters.prepare m a.lambda k Qv
  GeneralPaperEncodedSharedSource.profile W k Qv a weights Bc Br+GeneralPaperEpochResidentStorage.profile W m a.lambda k Qv+
    2*GeneralPaperActualProfitTreeStorage.profile W m a.lambda k Qv prepared+
    2*GeneralPaperNativeSelectorOutputStorage.profile W m ((GeneralPaperSourceParameters.prepare k).summarySize+2)
      prepared.grid.size prepared.parameters.height

theorem actual {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time count : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) (hc : count≤m) :
    window bits index price W A k Qv a (prepare a k Qv weights Bc Br) weights Bc Br epoch time count hc≤
      profile W k Qv a weights Bc Br := by
  let shared := prepare a k Qv weights Bc Br
  let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
  let cache := GeneralPaperCatalogueShared.cache shared a k trees
  let current := epochRun shared a k trees
  let before := beforeAt current time
  let cp := FixedArrayTable.ofFn (fun j => (before.read j).lambda.cdf)
  let rp := FixedArrayTable.ofFn (fun j => (before.read j).mu.cdf)
  have hbase := GeneralPaperSharedResidentStorage.actual W k Qv a weights Bc Br epoch time he ht
  have htrees := GeneralPaperActualProfitTreeStorage.epoch W k Qv a weights Bc Br hWeights epoch time ht
  have hca : cache.candidate.alphabet=a := by rw [cache.candidate_spec]; rfl
  have hra : cache.response.alphabet=a := by rw [cache.response_spec]; rfl
  have hctree := htrees.1.1
  have hrtree := htrees.2.1
  change GeneralPaperActualProfitTreeStorage.window W current.T current.profit cache.candidate weights cp≤
    GeneralPaperActualProfitTreeStorage.profile W m cache.candidate.alphabet.lambda k Qv current.profit at hctree
  change GeneralPaperActualProfitTreeStorage.window W current.T current.profit cache.response weights rp≤
    GeneralPaperActualProfitTreeStorage.profile W m cache.response.alphabet.lambda k Qv current.profit at hrtree
  rw [hca] at hctree
  rw [hra] at hrtree
  have hcoutput := GeneralPaperNativeSelectorOutputStorage.native bits index price W A current.profit current.T
    cache.candidate weights cp Bc count hc
  have hroutput := GeneralPaperNativeSelectorOutputStorage.native bits index price W A current.profit current.T
    cache.response weights rp Br count hc
  have total := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hbase hctree) hrtree) hcoutput) hroutput
  exact total.trans_eq (by
    unfold profile
    dsimp only
    rw [show current.profit=GeneralPaperProfitParameters.prepare m a.lambda k Qv from rfl]
    ring)

theorem prepared {m : ℕ} (model : RationalCostModel) (bits : Bool) (index price : ℕ → ℕ) (W A k Qv : ℕ)
    (b : ℚ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time count : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period)
    (hc : count≤m) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    window bits index price W A k Qv ready.1.1.1.2 ready.1.2 weights Bc Br epoch time count hc≤
      profile W k Qv ready.1.1.1.2 weights Bc Br := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact actual bits index price W A k Qv (GeneralPaperProxyParameters.alphabet m k) weights Bc Br hWeights epoch time count he ht hc

theorem retained_first_trajectory {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br firstBc firstBr : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time count : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) (hc : count≤m) :
    let first := prepare a k Qv weights firstBc firstBr
    GeneralPaperEncodedTrajectoryStorage.footprint W first.trajectory.rows
        (GeneralPaperCatalogueOuterLoop.execute first a k first.trajectory.epochs).2+
      window bits index price W A k Qv a (prepare a k Qv weights Bc Br) weights Bc Br epoch time count hc≤
      GeneralPaperEncodedTrajectoryStorage.profile W m a.lambda k+profile W k Qv a weights Bc Br :=
  Nat.add_le_add (GeneralPaperEncodedTrajectoryStorage.actual W k Qv a weights firstBc firstBr _ (Nat.le_refl _))
    (actual bits index price W A k Qv a weights Bc Br hWeights epoch time count he ht hc)

end Blotto.GeneralPaperSelectorResidentStorage
