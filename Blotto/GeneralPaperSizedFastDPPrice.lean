import Blotto.GeneralPaperFastDPParameterSizes

/-! The actual DP price now uses derived inverse-accuracy grid/option bounds,
with polynomial logarithmic factors in the retained source measure M. Native
Fin indices and dependent tree heights stay unchanged; only closed scalar
upper bounds are enlarged. Both reached selectors and prepared sources join. -/
namespace Blotto.GeneralPaperSizedFastDPPrice
open GeneralPaperFastRationalModel GeneralPaperFastOrderedDPPrice GeneralPaperFastDPParameterSizes
open GeneralPaperCatalogueEpochRun GeneralPaperCatalogueEpochCache
open GeneralPaperUnsignedCellConstancy (Prefix)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem field_profile_mono (C d W m lambda k Qv K J K' J' s : ℕ) (hK : K≤K') (hJ : J≤J') :
    fieldProfile C d W m lambda k Qv K J s≤fieldProfile C d W m lambda k Qv K' J' s := by
  unfold fieldProfile GeneralPaperOrderedDPAggregatePrice.leafBase GeneralPaperOrderedDPAggregatePrice.mergeBase
    GeneralPaperDPTableControls.emptyProfile GeneralPaperDPTableControls.labelsProfile GeneralPaperSummaryArrayExecution.arrayWord
  gcongr <;> exact binaryWordWidth_mono (by omega)

def profile (C d W m lambda k Qv : ℕ) : ℕ :=
  fieldProfile C d W m lambda k Qv (optionCap k) (gridCap m lambda k Qv) (lambda+1)

def Prices {m k : ℕ} (C d : ℕ) (model : RationalCostModel) (W Qv T : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (ready : GeneralPaperCatalogueOptimizer.Ready m k)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k)) : Prop :=
  let tree := GeneralPaperOrderedNativeProfitOptimizer.inputTree prepared T weights prefixes ready.cached
  (GeneralPaperOrderedDPExecution.run true (fun x => x) model.rat W prepared.grid tree).2≤
    profile C d W m ready.alphabet.lambda k Qv

theorem prices_of_checked {m k : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W Qv T : ℕ) (prepared : GeneralPaperProfitParameters.Prepared) (ready : GeneralPaperCatalogueOptimizer.Ready m k)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k))
    (hp : prepared=GeneralPaperProfitParameters.prepare m ready.alphabet.lambda k Qv)
    (checked : GeneralPaperActualOrderedDPPrice.Prices model W Qv T prepared ready weights prefixes) :
    Prices C d model W Qv T prepared ready weights prefixes := by
  have hn := GeneralPaperActualFastOrderedDPPrice.prices_of_checked hg W Qv T prepared ready weights prefixes hp checked
  have hj : prepared.grid.size≤gridCap m ready.alphabet.lambda k Qv := by rw [hp]; exact grid_size m ready.alphabet.lambda k Qv
  exact hn.trans (field_profile_mono C d W m ready.alphabet.lambda k Qv _ _ _ _ _ (options k) hj)

def Both {m k : ℕ} {cache : Cache m k} (C d : ℕ) (model : RationalCostModel) (W Qv : ℕ)
    (current : Run cache) (before : FixedArrayTable m (GeneralPaperEpochSnapshot.Snapshot k)) : Prop :=
  Prices C d model W Qv current.T current.profit cache.candidate current.weights (FixedArrayTable.ofFn (fun j => (before.read j).lambda.cdf)) ∧
    Prices C d model W Qv current.T current.profit cache.response current.weights (FixedArrayTable.ofFn (fun j => (before.read j).mu.cdf))

theorem both_work {m k : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W Qv : ℕ) (cache : Cache m k) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hw : ∑ j,weights.read j=Qv) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) :
    Both C d model W Qv (selected cache Qv weights Bc Br) (beforeAt (selected cache Qv weights Bc Br) time) := by
  have hca : cache.candidate.alphabet=cache.alphabet := by rw [cache.candidate_spec]; rfl
  have hra : cache.response.alphabet=cache.alphabet := by rw [cache.response_spec]; rfl
  have checked := GeneralPaperActualOrderedDPPrice.both_work model W Qv cache weights Bc Br hw time ht
  exact ⟨prices_of_checked hg W Qv _ _ _ _ _ (by rw [hca]; rfl) checked.1,
    prices_of_checked hg W Qv _ _ _ _ _ (by rw [hra]; rfl) checked.2⟩

theorem epoch_both_work {m : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W k Qv : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hw : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    let shared := GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br
    let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
    let current := GeneralPaperCatalogueShared.epochRun shared a k trees
    Both C d model W Qv current (beforeAt current time) := by
  dsimp only
  rw [GeneralPaperCatalogueShared.epochRun_selected]
  exact both_work hg W Qv _ weights Bc Br hw time ht

theorem prepared_both_work {m : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W k Qv : ℕ) (b : ℚ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hw : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let shared := ready.1.2
    let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
    let current := GeneralPaperCatalogueShared.epochRun shared a k trees
    Both C d model W Qv current (beforeAt current time) := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact epoch_both_work hg W k Qv (GeneralPaperProxyParameters.alphabet m k) weights Bc Br hw epoch time ht

end Blotto.GeneralPaperSizedFastDPPrice
