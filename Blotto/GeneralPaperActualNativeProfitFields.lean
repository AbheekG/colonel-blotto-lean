import Blotto.GeneralPaperNativeProfitFieldsPrice

/-! Both source optimizers use their retained prepared plans and reached
signed-block prefixes. The actual rounded-value sum derives each weight cap;
no weight census, profit rebuild or tag calibration pass is introduced.
-/
namespace Blotto.GeneralPaperActualNativeProfitFields
open scoped BigOperators
open GeneralPaperCatalogueEpochRun GeneralPaperCatalogueEpochCache
open GeneralPaperUnsignedCellConstancy (Prefix)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

theorem meshes {m k : ℕ} (ready : GeneralPaperCatalogueOptimizer.Ready m k) (j : Fin m) :
    (ready.cached.read j).mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator := by
  rw [ready.cached_spec,GeneralPaperOrderedNativeProfitOptimizer.plans,FixedArrayTable.read_ofFn]
  rfl

theorem data {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W T : ℕ) (ready : GeneralPaperCatalogueOptimizer.Ready m k)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k)) :
    (GeneralPaperNativeProfitFieldsExecution.run bits index price W T weights prefixes ready.cached).1=
      GeneralPaperOrderedNativeProfitOptimizer.weightedFields k T weights prefixes ready.cached :=
  GeneralPaperNativeProfitFieldsExecution.data bits index price W T weights prefixes ready.cached (meshes ready)

theorem work {m k : ℕ} (model : RationalCostModel) (W lambda Qv T : ℕ) (ready : GeneralPaperCatalogueOptimizer.Ready m k)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k))
    (hT : T=(GeneralPaperTrajectoryParameters.prepare lambda k).rows) (hWeights : ∑ j,weights.read j=Qv)
    (hGood : ∀ j,GeneralPaperMeshPrefixInvariant.Good m lambda k Qv (prefixes.read j)) :
    (GeneralPaperNativeProfitFieldsExecution.run true (fun w => w) model.rat W T weights prefixes ready.cached).2≤
      GeneralPaperNativeProfitFieldsPrice.profile model.rat W m lambda k Qv ((GeneralPaperSourceParameters.prepare k).summarySize+2) ∧
    (GeneralPaperNativeProfitFieldsExecution.run false (fun _ => 1) model.rat 1 T weights prefixes ready.cached).2≤
      GeneralPaperNativeProfitFieldsPrice.arithmeticProfile m ((GeneralPaperSourceParameters.prepare k).summarySize+2) k :=
  ⟨GeneralPaperNativeProfitFieldsPrice.bit_work model.rat model.monotone W lambda Qv T weights prefixes ready.cached hT hWeights (meshes ready) hGood,
    GeneralPaperNativeProfitFieldsPrice.arithmetic_work model.rat T weights prefixes ready.cached⟩

theorem both_work {m k : ℕ} (model : RationalCostModel) (W Qv : ℕ) (cache : Cache m k)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) :
    let current := selected cache Qv weights Bc Br
    let before := beforeAt current time
    let candidatePrefix := FixedArrayTable.ofFn (fun j => (before.read j).lambda.cdf)
    let responsePrefix := FixedArrayTable.ofFn (fun j => (before.read j).mu.cdf)
    let T := (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).rows
    let K := (GeneralPaperSourceParameters.prepare k).summarySize+2
    ((GeneralPaperNativeProfitFieldsExecution.run true (fun w => w) model.rat W T weights candidatePrefix cache.candidate.cached).2≤
        GeneralPaperNativeProfitFieldsPrice.profile model.rat W m cache.alphabet.lambda k Qv K ∧
      (GeneralPaperNativeProfitFieldsExecution.run false (fun _ => 1) model.rat 1 T weights candidatePrefix cache.candidate.cached).2≤
        GeneralPaperNativeProfitFieldsPrice.arithmeticProfile m K k) ∧
    ((GeneralPaperNativeProfitFieldsExecution.run true (fun w => w) model.rat W T weights responsePrefix cache.response.cached).2≤
        GeneralPaperNativeProfitFieldsPrice.profile model.rat W m cache.alphabet.lambda k Qv K ∧
      (GeneralPaperNativeProfitFieldsExecution.run false (fun _ => 1) model.rat 1 T weights responsePrefix cache.response.cached).2≤
        GeneralPaperNativeProfitFieldsPrice.arithmeticProfile m K k) := by
  have hc := work model W cache.alphabet.lambda Qv _ cache.candidate weights
    (FixedArrayTable.ofFn (fun j => ((beforeAt (selected cache Qv weights Bc Br) time).read j).lambda.cdf)) rfl hWeights
    (by
      intro j
      rw [FixedArrayTable.read_ofFn]
      exact GeneralPaperActualMeshPrefixInvariant.selected_good cache Qv weights Bc Br time ht j .lambda)
  have hr := work model W cache.alphabet.lambda Qv _ cache.response weights
    (FixedArrayTable.ofFn (fun j => ((beforeAt (selected cache Qv weights Bc Br) time).read j).mu.cdf)) rfl hWeights
    (by
      intro j
      rw [FixedArrayTable.read_ofFn]
      exact GeneralPaperActualMeshPrefixInvariant.selected_good cache Qv weights Bc Br time ht j .mu)
  exact ⟨hc,hr⟩

theorem epoch_both_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    let shared := GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br
    let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
    let cache := GeneralPaperCatalogueShared.cache shared a k trees
    let current := GeneralPaperCatalogueShared.epochRun shared a k trees
    let before := beforeAt current time
    let candidatePrefix := FixedArrayTable.ofFn (fun j => (before.read j).lambda.cdf)
    let responsePrefix := FixedArrayTable.ofFn (fun j => (before.read j).mu.cdf)
    let T := shared.trajectory.rows
    let K := (GeneralPaperSourceParameters.prepare k).summarySize+2
    ((GeneralPaperNativeProfitFieldsExecution.run true (fun w => w) model.rat W T weights candidatePrefix cache.candidate.cached).2≤
        GeneralPaperNativeProfitFieldsPrice.profile model.rat W m a.lambda k Qv K ∧
      (GeneralPaperNativeProfitFieldsExecution.run false (fun _ => 1) model.rat 1 T weights candidatePrefix cache.candidate.cached).2≤
        GeneralPaperNativeProfitFieldsPrice.arithmeticProfile m K k) ∧
    ((GeneralPaperNativeProfitFieldsExecution.run true (fun w => w) model.rat W T weights responsePrefix cache.response.cached).2≤
        GeneralPaperNativeProfitFieldsPrice.profile model.rat W m a.lambda k Qv K ∧
      (GeneralPaperNativeProfitFieldsExecution.run false (fun _ => 1) model.rat 1 T weights responsePrefix cache.response.cached).2≤
        GeneralPaperNativeProfitFieldsPrice.arithmeticProfile m K k) := by
  dsimp only
  rw [GeneralPaperCatalogueShared.epochRun_selected]
  let shared := GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br
  let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
  exact both_work model W Qv (GeneralPaperCatalogueShared.cache shared a k trees) weights Bc Br hWeights time ht

theorem prepared_both_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (b : ℚ) (weights : FixedArrayTable m ℕ)
    (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).period) :
    let ready := (GeneralPaperPreparedSharedSource.prepare model k Qv b weights Bc Br).1
    let a := ready.1.1.1.2
    let shared := ready.1.2
    let trees := GeneralPaperCatalogueOuterLoop.treesAt shared a k epoch
    let cache := GeneralPaperCatalogueShared.cache shared a k trees
    let current := GeneralPaperCatalogueShared.epochRun shared a k trees
    let before := beforeAt current time
    let candidatePrefix := FixedArrayTable.ofFn (fun j => (before.read j).lambda.cdf)
    let responsePrefix := FixedArrayTable.ofFn (fun j => (before.read j).mu.cdf)
    let T := shared.trajectory.rows
    let K := (GeneralPaperSourceParameters.prepare k).summarySize+2
    ((GeneralPaperNativeProfitFieldsExecution.run true (fun w => w) model.rat W T weights candidatePrefix cache.candidate.cached).2≤
        GeneralPaperNativeProfitFieldsPrice.profile model.rat W m a.lambda k Qv K ∧
      (GeneralPaperNativeProfitFieldsExecution.run false (fun _ => 1) model.rat 1 T weights candidatePrefix cache.candidate.cached).2≤
        GeneralPaperNativeProfitFieldsPrice.arithmeticProfile m K k) ∧
    ((GeneralPaperNativeProfitFieldsExecution.run true (fun w => w) model.rat W T weights responsePrefix cache.response.cached).2≤
        GeneralPaperNativeProfitFieldsPrice.profile model.rat W m a.lambda k Qv K ∧
      (GeneralPaperNativeProfitFieldsExecution.run false (fun _ => 1) model.rat 1 T weights responsePrefix cache.response.cached).2≤
        GeneralPaperNativeProfitFieldsPrice.arithmeticProfile m K k) := by
  dsimp only
  rw [GeneralPaperPreparedSharedSource.data]
  exact epoch_both_work model W k Qv (GeneralPaperProxyParameters.alphabet m k) weights Bc Br hWeights epoch time ht

end Blotto.GeneralPaperActualNativeProfitFields
