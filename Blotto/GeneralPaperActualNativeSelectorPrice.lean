import Blotto.GeneralPaperNativeSelectorPrice

/-! Both complete native row pickers use literal budgets and reached signed prefixes
and retained grids/options. These joins derive all word/profit premises;
they do not rebuild an input tree, query a selector or execute a DP twice. -/
namespace Blotto.GeneralPaperActualNativeSelectorPrice
open GeneralPaperCatalogueEpochRun GeneralPaperCatalogueEpochCache
open GeneralPaperUnsignedCellConstancy (Prefix)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def Prices {m k : ℕ} (model : RationalCostModel) (W Qv T : ℕ) (prepared : GeneralPaperProfitParameters.Prepared)
    (ready : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k)) (B : ℚ) : Prop :=
  let K := (GeneralPaperSourceParameters.prepare k).summarySize+2
  (GeneralPaperNativeSelectorExecution.pick true (fun x => x) model.rat W prepared T ready weights prefixes B).2≤
    GeneralPaperNativeSelectorPrice.pickProfile model W m ready.alphabet.lambda k Qv K prepared.grid.size
      prepared.parameters.height prepared.parameters.leafCount (rationalWordWidth B) ∧
  (GeneralPaperNativeSelectorExecution.pick false (fun _ => 1) model.rat 1 prepared T ready weights prefixes B).2≤
    GeneralPaperNativeSelectorPrice.pickArithmeticProfile m k K prepared.grid.size prepared.grid.depth
      prepared.parameters.height prepared.parameters.leafCount

def Both {m k : ℕ} {cache : Cache m k} (model : RationalCostModel) (W Qv : ℕ)
    (current : Run cache) (before : FixedArrayTable m (GeneralPaperEpochSnapshot.Snapshot k)) : Prop :=
  Prices model W Qv current.T current.profit cache.candidate current.weights (FixedArrayTable.ofFn (fun j => (before.read j).lambda.cdf)) current.Bc ∧
  Prices model W Qv current.T current.profit cache.response current.weights (FixedArrayTable.ofFn (fun j => (before.read j).mu.cdf)) current.Br

theorem both_work {m k : ℕ} (model : RationalCostModel) (W Qv : ℕ) (cache : Cache m k)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) :
    Both model W Qv (selected cache Qv weights Bc Br) (beforeAt (selected cache Qv weights Bc Br) time) := by
  have hca : cache.candidate.alphabet=cache.alphabet := by rw [cache.candidate_spec]; rfl
  have hra : cache.response.alphabet=cache.alphabet := by rw [cache.response_spec]; rfl
  have hc := GeneralPaperNativeSelectorPrice.native_work model W Qv (selected cache Qv weights Bc Br).T
    (selected cache Qv weights Bc Br).profit cache.candidate weights
    (FixedArrayTable.ofFn (fun j => ((beforeAt (selected cache Qv weights Bc Br) time).read j).lambda.cdf)) Bc
    (by rw [hca]; rfl) (by rw [hca]; rfl) hWeights (by
      intro j
      rw [hca,FixedArrayTable.read_ofFn]
      exact GeneralPaperActualMeshPrefixInvariant.selected_good cache Qv weights Bc Br time ht j .lambda)
  have hr := GeneralPaperNativeSelectorPrice.native_work model W Qv (selected cache Qv weights Bc Br).T
    (selected cache Qv weights Bc Br).profit cache.response weights
    (FixedArrayTable.ofFn (fun j => ((beforeAt (selected cache Qv weights Bc Br) time).read j).mu.cdf)) Br
    (by rw [hra]; rfl) (by rw [hra]; rfl) hWeights (by
      intro j
      rw [hra,FixedArrayTable.read_ofFn]
      exact GeneralPaperActualMeshPrefixInvariant.selected_good cache Qv weights Bc Br time ht j .mu)
  exact ⟨hc,hr⟩

theorem epoch_both_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    let shared := GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br
    let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
    let current := GeneralPaperCatalogueShared.epochRun shared a k trees
    Both model W Qv current (beforeAt current time) := by
  dsimp only
  rw [GeneralPaperCatalogueShared.epochRun_selected]
  let shared := GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br
  let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
  exact both_work model W Qv (GeneralPaperCatalogueShared.cache shared a k trees) weights Bc Br hWeights time ht

theorem prepared_both_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let shared := ready.1.2
    let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
    let current := GeneralPaperCatalogueShared.epochRun shared a k trees
    Both model W Qv current (beforeAt current time) := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact epoch_both_work model W k Qv (GeneralPaperProxyParameters.alphabet m k) weights Bc Br hWeights epoch time ht

end Blotto.GeneralPaperActualNativeSelectorPrice
