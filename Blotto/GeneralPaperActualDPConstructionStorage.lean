import Blotto.GeneralPaperDPConstructionStorage

/-! Actual Ready catalogues derive every leaf-height premise for DP
construction, at reached source and prepared-source callers. Streaming DP
phase windows coexist with the source/selector residents already bounded.
Primitive callback scratch and other construction/query phases remain open. -/
namespace Blotto.GeneralPaperActualDPConstructionStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochRun
open GeneralPaperUnsignedCellConstancy (Prefix)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem ready {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (T : ℕ) (r : GeneralPaperCatalogueOptimizer.Ready m k)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k)) :
    GeneralPaperDPConstructionStorage.peak bits index price W prepared.grid
      (GeneralPaperOrderedNativeProfitOptimizer.inputTree prepared T weights prefixes r.cached)≤
      GeneralPaperDPConstructionStorage.profile W ((GeneralPaperSourceParameters.prepare k).summarySize+2)
        prepared.grid.size (r.alphabet.lambda+1) prepared.parameters.height :=
  GeneralPaperDPConstructionStorage.native bits index price W (r.alphabet.lambda+1) prepared.grid _
    (GeneralPaperOrderedDPHeight.native_tree prepared T r weights prefixes)

theorem prepared_tree {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (T : ℕ) (r : GeneralPaperCatalogueOptimizer.Ready m k)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k))
    (hs : prepared.parameters.leafCount=2^prepared.parameters.height) :
    GeneralPaperDPConstructionStorage.peak bits index price W prepared.grid
      (GeneralPaperNativeSelectorExecution.prepareTree bits index price W prepared T r weights prefixes).1≤
      GeneralPaperDPConstructionStorage.profile W ((GeneralPaperSourceParameters.prepare k).summarySize+2)
        prepared.grid.size (r.alphabet.lambda+1) prepared.parameters.height := by
  rw [GeneralPaperNativeSelectorExecution.prepareTree_data bits index price W prepared T r weights prefixes hs]
  exact ready bits index price W prepared T r weights prefixes

def Both {m k : ℕ} {cache : GeneralPaperCatalogueEpochCache.Cache m k} (bits : Bool) (index price : ℕ → ℕ)
    (W : ℕ) (current : Run cache) (before : FixedArrayTable m (GeneralPaperEpochSnapshot.Snapshot k)) : Prop :=
  GeneralPaperDPConstructionStorage.peak bits index price W current.profit.grid
      (GeneralPaperOrderedNativeProfitOptimizer.inputTree current.profit current.T current.weights
        (FixedArrayTable.ofFn (fun j => (before.read j).lambda.cdf)) cache.candidate.cached)≤
    GeneralPaperDPConstructionStorage.profile W ((GeneralPaperSourceParameters.prepare k).summarySize+2)
      current.profit.grid.size (cache.candidate.alphabet.lambda+1) current.profit.parameters.height ∧
  GeneralPaperDPConstructionStorage.peak bits index price W current.profit.grid
      (GeneralPaperOrderedNativeProfitOptimizer.inputTree current.profit current.T current.weights
        (FixedArrayTable.ofFn (fun j => (before.read j).mu.cdf)) cache.response.cached)≤
    GeneralPaperDPConstructionStorage.profile W ((GeneralPaperSourceParameters.prepare k).summarySize+2)
      current.profit.grid.size (cache.response.alphabet.lambda+1) current.profit.parameters.height

theorem both {m k : ℕ} {cache : GeneralPaperCatalogueEpochCache.Cache m k} (bits : Bool) (index price : ℕ → ℕ)
    (W : ℕ) (current : Run cache) (before : FixedArrayTable m (GeneralPaperEpochSnapshot.Snapshot k)) :
    Both bits index price W current before :=
  ⟨ready bits index price W current.profit current.T cache.candidate current.weights
    (FixedArrayTable.ofFn (fun j => (before.read j).lambda.cdf)),
    ready bits index price W current.profit current.T cache.response current.weights
    (FixedArrayTable.ofFn (fun j => (before.read j).mu.cdf))⟩

def window {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A k Qv : ℕ) (a : Alphabet)
    (shared : Shared m) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time count : ℕ) (hc : count≤m) : ℕ :=
  let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
  let cache := GeneralPaperCatalogueShared.cache shared a k trees
  let current := epochRun shared a k trees
  let before := beforeAt current time
  GeneralPaperSelectorResidentStorage.window bits index price W A k Qv a shared weights Bc Br epoch time count hc+
    GeneralPaperDPConstructionStorage.peak bits index price W current.profit.grid
      (GeneralPaperOrderedNativeProfitOptimizer.inputTree current.profit current.T weights
        (FixedArrayTable.ofFn (fun j => (before.read j).lambda.cdf)) cache.candidate.cached)+
    GeneralPaperDPConstructionStorage.peak bits index price W current.profit.grid
      (GeneralPaperOrderedNativeProfitOptimizer.inputTree current.profit current.T weights
        (FixedArrayTable.ofFn (fun j => (before.read j).mu.cdf)) cache.response.cached)

def profile {m : ℕ} (W k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : ℕ :=
  let p := GeneralPaperProfitParameters.prepare m a.lambda k Qv
  GeneralPaperSelectorResidentStorage.profile W k Qv a weights Bc Br+
    2*GeneralPaperDPConstructionStorage.profile W ((GeneralPaperSourceParameters.prepare k).summarySize+2)
      p.grid.size (a.lambda+1) p.parameters.height

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
  have hbase := GeneralPaperSelectorResidentStorage.actual bits index price W A k Qv a weights Bc Br hWeights epoch time count he ht hc
  have hb := both bits index price W current before
  have hca : cache.candidate.alphabet=a := by rw [cache.candidate_spec]; rfl
  have hra : cache.response.alphabet=a := by rw [cache.response_spec]; rfl
  have hcp := hb.1
  have hrp := hb.2
  change _≤GeneralPaperDPConstructionStorage.profile W ((GeneralPaperSourceParameters.prepare k).summarySize+2)
    current.profit.grid.size (cache.candidate.alphabet.lambda+1) current.profit.parameters.height at hcp
  change _≤GeneralPaperDPConstructionStorage.profile W ((GeneralPaperSourceParameters.prepare k).summarySize+2)
    current.profit.grid.size (cache.response.alphabet.lambda+1) current.profit.parameters.height at hrp
  rw [hca] at hcp
  rw [hra] at hrp
  have total := Nat.add_le_add (Nat.add_le_add hbase hcp) hrp
  exact total.trans_eq (by
    unfold profile
    dsimp only
    rw [show current.profit=GeneralPaperProfitParameters.prepare m a.lambda k Qv from rfl]
    ring)

theorem prepared {m : ℕ} (model : RationalCostModel) (bits : Bool) (index price : ℕ → ℕ) (W A k Qv : ℕ)
    (b : ℚ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time count : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period) (hc : count≤m) :
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

end Blotto.GeneralPaperActualDPConstructionStorage
