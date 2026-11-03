import Blotto.GeneralPaperProfitTreeConstructionStorage

/-! Actual candidate/response prefixes close the native profit-input,
balanced-tree/DP coexistence and split-construction frame bounds. Exact
DP resources still use their subtree-height profile. This does not claim
root/decode/trim, field/padding construction or primitive scratch peaks. -/
namespace Blotto.GeneralPaperActualProfitTreeStorage
open scoped BigOperators
open GeneralPaperResponseTag GeneralPaperCatalogueEpochRun GeneralPaperCatalogueEpochCache
open GeneralPaperUnsignedCellConstancy (Prefix)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def window {m k : ℕ} (W T : ℕ) (prepared : GeneralPaperProfitParameters.Prepared)
    (r : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (Prefix k)) : ℕ :=
  let input := GeneralPaperOrderedNativeProfitOptimizer.weightedFields k T weights prefixes r.cached
  let tree := GeneralPaperOrderedNativeProfitOptimizer.inputTree prepared T weights prefixes r.cached
  GeneralPaperEncodedProfitInput.footprint W input+GeneralPaperEncodedProfitTree.footprint W tree+
    GeneralPaperEncodedDPStorage.footprint W (GeneralPaperOrderedProfitDP.run prepared.grid tree)

def profile (W m lambda k Qv : ℕ) (prepared : GeneralPaperProfitParameters.Prepared) : ℕ :=
  GeneralPaperEncodedProfitInput.profile W m lambda k Qv+
    2^prepared.parameters.height*(GeneralPaperEncodedProfitInput.fieldProfile W m lambda k Qv+64*W)+
    GeneralPaperEncodedDPStorage.profile W ((GeneralPaperSourceParameters.prepare k).summarySize+2)
      prepared.grid.size (lambda+1) prepared.parameters.height

def Bounds {m k : ℕ} (W Qv T : ℕ) (prepared : GeneralPaperProfitParameters.Prepared)
    (r : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (Prefix k)) : Prop :=
  window W T prepared r weights prefixes≤profile W m r.alphabet.lambda k Qv prepared ∧
  GeneralPaperProfitTreeConstructionStorage.peak W prepared.parameters.height
    (GeneralPaperOrderedProfitTreeBuild.pad prepared.parameters.height
      (GeneralPaperOrderedNativeProfitOptimizer.weightedFields k T weights prefixes r.cached))≤
    2^prepared.parameters.height*(GeneralPaperEncodedProfitInput.fieldProfile W m r.alphabet.lambda k Qv+64*W)+
      (prepared.parameters.height+1)*GeneralPaperProfitTreeConstructionStorage.frameProfile W prepared.parameters.height

theorem ready {m k : ℕ} (W Qv T : ℕ) (prepared : GeneralPaperProfitParameters.Prepared)
    (r : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (Prefix k))
    (hT : T=(GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows)
    (hPrepared : prepared=GeneralPaperProfitParameters.prepare m r.alphabet.lambda k Qv)
    (hWeights : ∑ j,weights.read j=Qv)
    (hGood : ∀ j,GeneralPaperMeshPrefixInvariant.Good m r.alphabet.lambda k Qv (prefixes.read j)) :
    Bounds W Qv T prepared r weights prefixes := by
  subst T
  let input := GeneralPaperOrderedNativeProfitOptimizer.weightedFields k
    (GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows weights prefixes r.cached
  let F := GeneralPaperEncodedProfitInput.fieldProfile W m r.alphabet.lambda k Qv
  have hInput := GeneralPaperEncodedProfitInput.native W Qv r weights prefixes hWeights hGood
  have hTree := GeneralPaperEncodedProfitTree.ready W Qv prepared r weights prefixes hWeights hGood
  have hDP := GeneralPaperEncodedDPStorage.ready W prepared
    (GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows r weights prefixes
  have hFit : input.length≤2^prepared.parameters.height := by
    rw [GeneralPaperOrderedNativeProfitOptimizer.weighted_length,hPrepared]
    change m≤2^(GeneralPaperProfitParameters.parameters m r.alphabet.lambda k Qv).height
    have hc := GeneralPaperProfitParameters.covers_fields m r.alphabet.lambda k Qv
    rw [GeneralPaperProfitParameters.leaf_count_spec] at hc
    exact hc
  have hZero : GeneralPaperEncodedProfitField.footprint W
      (GeneralPaperOrderedProfitTreeBuild.dummy Tag ((GeneralPaperSourceParameters.prepare k).summarySize+2)).1≤F := by
    apply GeneralPaperEncodedProfitField.dummy
    · have hM := (GeneralPaperSourcePreparationEnvelope.base m r.alphabet.lambda k Qv).2
      unfold GeneralPaperPowerPreparationEnvelope.operandWidth
      omega
    · omega
  have hFields := GeneralPaperEncodedProfitInput.native_field W Qv r weights prefixes hWeights hGood
  have hPeak := GeneralPaperProfitTreeConstructionStorage.bounded W prepared.parameters.height F prepared.parameters.height
    (GeneralPaperOrderedProfitTreeBuild.pad prepared.parameters.height input) (Nat.le_refl _)
    (by rw [GeneralPaperOrderedProfitTreeBuild.pad_length _ input hFit]) hZero (by
      intro f hf
      rcases List.mem_append.mp hf with hf|hf
      · exact hFields f hf
      · have he := (List.mem_replicate.mp hf).2
        subst f
        exact hZero)
  exact ⟨Nat.add_le_add (Nat.add_le_add hInput hTree) hDP,hPeak⟩

def Both {m k : ℕ} {cache : Cache m k} (W Qv : ℕ) (current : Run cache)
    (before : FixedArrayTable m (GeneralPaperEpochSnapshot.Snapshot k)) : Prop :=
  Bounds W Qv current.T current.profit cache.candidate current.weights
    (FixedArrayTable.ofFn (fun j => (before.read j).lambda.cdf)) ∧
  Bounds W Qv current.T current.profit cache.response current.weights
    (FixedArrayTable.ofFn (fun j => (before.read j).mu.cdf))

theorem both {m k : ℕ} (W Qv : ℕ) (cache : Cache m k) (weights : FixedArrayTable m ℕ)
    (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) :
    Both W Qv (selected cache Qv weights Bc Br) (beforeAt (selected cache Qv weights Bc Br) time) := by
  have hca : cache.candidate.alphabet=cache.alphabet := by rw [cache.candidate_spec]; rfl
  have hra : cache.response.alphabet=cache.alphabet := by rw [cache.response_spec]; rfl
  have hc := ready W Qv (selected cache Qv weights Bc Br).T (selected cache Qv weights Bc Br).profit
    cache.candidate weights (FixedArrayTable.ofFn (fun j => ((beforeAt (selected cache Qv weights Bc Br) time).read j).lambda.cdf))
    (by rw [hca]; rfl) (by rw [hca]; rfl) hWeights (by
      intro j
      rw [hca,FixedArrayTable.read_ofFn]
      exact GeneralPaperActualMeshPrefixInvariant.selected_good cache Qv weights Bc Br time ht j .lambda)
  have hr := ready W Qv (selected cache Qv weights Bc Br).T (selected cache Qv weights Bc Br).profit
    cache.response weights (FixedArrayTable.ofFn (fun j => ((beforeAt (selected cache Qv weights Bc Br) time).read j).mu.cdf))
    (by rw [hra]; rfl) (by rw [hra]; rfl) hWeights (by
      intro j
      rw [hra,FixedArrayTable.read_ofFn]
      exact GeneralPaperActualMeshPrefixInvariant.selected_good cache Qv weights Bc Br time ht j .mu)
  exact ⟨hc,hr⟩

theorem epoch {m : ℕ} (W k Qv : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet) (weights : FixedArrayTable m ℕ)
    (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (count time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    let shared := GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br
    let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k count
    let current := GeneralPaperCatalogueShared.epochRun shared a k trees
    Both W Qv current (beforeAt current time) := by
  dsimp only
  rw [GeneralPaperCatalogueShared.epochRun_selected]
  let shared := GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br
  let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k count
  exact both W Qv (GeneralPaperCatalogueShared.cache shared a k trees) weights Bc Br hWeights time ht

theorem prepared {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ) (weights : FixedArrayTable m ℕ)
    (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (count time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let shared := ready.1.2
    let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k count
    let current := GeneralPaperCatalogueShared.epochRun shared a k trees
    Both W Qv current (beforeAt current time) := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact epoch W k Qv (GeneralPaperProxyParameters.alphabet m k) weights Bc Br hWeights count time ht

end Blotto.GeneralPaperActualProfitTreeStorage
