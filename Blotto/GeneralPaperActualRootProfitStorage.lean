import Blotto.GeneralPaperRootProfitPhaseStorage

/-! Actual reached signed prefixes and retained native preparations close
both root/profit construction windows. Their coexistence with the prior
source/selector/DP residents and first completed trajectory is explicit.
Query/primitive scratch, other initialization and global W remain open. -/
namespace Blotto.GeneralPaperActualRootProfitStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochRun
open GeneralPaperUnsignedCellConstancy (Prefix)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def Both {m k : ℕ} {cache : GeneralPaperCatalogueEpochCache.Cache m k} (bits : Bool) (index price : ℕ → ℕ)
    (W A Qv : ℕ) (current : Run cache) (before : FixedArrayTable m (GeneralPaperEpochSnapshot.Snapshot k))
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (count copied : ℕ) (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) : Prop :=
  GeneralPaperRootProfitPhaseStorage.window bits index price W A current.profit current.T cache.candidate current.weights
      (FixedArrayTable.ofFn (fun j => (before.read j).lambda.cdf)) current.Bc j i count copied hc≤
    GeneralPaperRootProfitPhaseStorage.profile W m cache.candidate.alphabet.lambda k Qv current.profit (rationalWordWidth current.Bc) ∧
  GeneralPaperRootProfitPhaseStorage.window bits index price W A current.profit current.T cache.response current.weights
      (FixedArrayTable.ofFn (fun j => (before.read j).mu.cdf)) current.Br j i count copied hc≤
    GeneralPaperRootProfitPhaseStorage.profile W m cache.response.alphabet.lambda k Qv current.profit (rationalWordWidth current.Br)

theorem both {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A Qv : ℕ)
    (cache : GeneralPaperCatalogueEpochCache.Cache m k) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hWeights : ∑ j,weights.read j=Qv) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (count copied : ℕ) (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) :
    Both bits index price W A Qv (selected cache Qv weights Bc Br) (beforeAt (selected cache Qv weights Bc Br) time) j i count copied hc := by
  have hca : cache.candidate.alphabet=cache.alphabet := by rw [cache.candidate_spec]; rfl
  have hra : cache.response.alphabet=cache.alphabet := by rw [cache.response_spec]; rfl
  have hp := GeneralPaperRootProfitPhaseStorage.ready bits index price W A Qv
    (selected cache Qv weights Bc Br).profit (selected cache Qv weights Bc Br).T cache.candidate weights
    (FixedArrayTable.ofFn (fun j => ((beforeAt (selected cache Qv weights Bc Br) time).read j).lambda.cdf)) Bc
    (by rw [hca]; rfl) (by rw [hca]; rfl) hWeights (by
      intro j
      rw [hca,FixedArrayTable.read_ofFn]
      exact GeneralPaperActualMeshPrefixInvariant.selected_good cache Qv weights Bc Br time ht j .lambda) j i count copied hc
  have hr := GeneralPaperRootProfitPhaseStorage.ready bits index price W A Qv
    (selected cache Qv weights Bc Br).profit (selected cache Qv weights Bc Br).T cache.response weights
    (FixedArrayTable.ofFn (fun j => ((beforeAt (selected cache Qv weights Bc Br) time).read j).mu.cdf)) Br
    (by rw [hra]; rfl) (by rw [hra]; rfl) hWeights (by
      intro j
      rw [hra,FixedArrayTable.read_ofFn]
      exact GeneralPaperActualMeshPrefixInvariant.selected_good cache Qv weights Bc Br time ht j .mu) j i count copied hc
  exact ⟨hp,hr⟩

def window {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A k Qv : ℕ) (a : Alphabet)
    (shared : Shared m) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count copied rowCount : ℕ)
    (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m) : ℕ :=
  let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
  let cache := GeneralPaperCatalogueShared.cache shared a k trees
  let current := epochRun shared a k trees
  let before := beforeAt current time
  GeneralPaperActualDPConstructionStorage.window bits index price W A k Qv a shared weights Bc Br epoch time rowCount hr+
    GeneralPaperRootProfitPhaseStorage.window bits index price W A current.profit current.T cache.candidate weights
      (FixedArrayTable.ofFn (fun j => (before.read j).lambda.cdf)) Bc j i count copied hc+
    GeneralPaperRootProfitPhaseStorage.window bits index price W A current.profit current.T cache.response weights
      (FixedArrayTable.ofFn (fun j => (before.read j).mu.cdf)) Br j i count copied hc

def profile {m : ℕ} (W k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) : ℕ :=
  let p := GeneralPaperProfitParameters.prepare m a.lambda k Qv
  GeneralPaperActualDPConstructionStorage.profile W k Qv a weights Bc Br+
    GeneralPaperRootProfitPhaseStorage.profile W m a.lambda k Qv p (rationalWordWidth Bc)+
    GeneralPaperRootProfitPhaseStorage.profile W m a.lambda k Qv p (rationalWordWidth Br)

theorem actual {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count copied rowCount : ℕ)
    (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m) :
    window bits index price W A k Qv a (prepare a k Qv weights Bc Br) weights Bc Br epoch time j i count copied rowCount hc hr≤
      profile W k Qv a weights Bc Br := by
  let shared := prepare a k Qv weights Bc Br
  let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
  let cache := GeneralPaperCatalogueShared.cache shared a k trees
  let current := epochRun shared a k trees
  have hbase := GeneralPaperActualDPConstructionStorage.actual bits index price W A k Qv a weights Bc Br hWeights epoch time rowCount he ht hr
  have hp := both bits index price W A Qv cache weights Bc Br hWeights time ht j i count copied hc
  have hcp := hp.1
  have hrp := hp.2
  have hca : cache.candidate.alphabet=a := by rw [cache.candidate_spec]; rfl
  have hra : cache.response.alphabet=a := by rw [cache.response_spec]; rfl
  change _≤GeneralPaperRootProfitPhaseStorage.profile W m cache.candidate.alphabet.lambda k Qv current.profit (rationalWordWidth Bc) at hcp
  change _≤GeneralPaperRootProfitPhaseStorage.profile W m cache.response.alphabet.lambda k Qv current.profit (rationalWordWidth Br) at hrp
  rw [hca] at hcp
  rw [hra] at hrp
  have total := Nat.add_le_add (Nat.add_le_add hbase hcp) hrp
  exact total.trans_eq (by
    unfold profile
    dsimp only
    rw [show current.profit=GeneralPaperProfitParameters.prepare m a.lambda k Qv from rfl])

theorem prepared {m : ℕ} (model : RationalCostModel) (bits : Bool) (index price : ℕ → ℕ) (W A k Qv : ℕ)
    (b : ℚ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count copied rowCount : ℕ)
    (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    window bits index price W A k Qv ready.1.1.1.2 ready.1.2 weights Bc Br epoch time j i count copied rowCount hc hr≤
      profile W k Qv ready.1.1.1.2 weights Bc Br := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact actual bits index price W A k Qv (GeneralPaperProxyParameters.alphabet m k) weights Bc Br hWeights epoch time he ht j i count copied rowCount hc hr

theorem retained_first_trajectory {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br firstBc firstBr : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) (count copied rowCount : ℕ)
    (hc : count≤(GeneralPaperSourceParameters.prepare k).summarySize+2) (hr : rowCount≤m) :
    let first := prepare a k Qv weights firstBc firstBr
    GeneralPaperEncodedTrajectoryStorage.footprint W first.trajectory.rows
        (GeneralPaperCatalogueOuterLoop.execute first a k first.trajectory.epochs).2+
      window bits index price W A k Qv a (prepare a k Qv weights Bc Br) weights Bc Br epoch time j i count copied rowCount hc hr≤
      GeneralPaperEncodedTrajectoryStorage.profile W m a.lambda k+profile W k Qv a weights Bc Br :=
  Nat.add_le_add (GeneralPaperEncodedTrajectoryStorage.actual W k Qv a weights firstBc firstBr _ (Nat.le_refl _))
    (actual bits index price W A k Qv a weights Bc Br hWeights epoch time he ht j i count copied rowCount hc hr)

end Blotto.GeneralPaperActualRootProfitStorage
