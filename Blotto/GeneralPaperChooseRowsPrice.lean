import Blotto.GeneralPaperChooseRowsExecution

/-! Complete two-selector prices include their shared prefix views once.
Actual reached snapshots supply both signed-block query invariants. -/
namespace Blotto.GeneralPaperChooseRowsPrice
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRun
open GeneralPaperUnsignedCellConstancy (Prefix)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000

def profile (model : RationalCostModel) (W m lambda k Qv J height leaves BcWord BrWord : ℕ) : ℕ :=
  let K := (GeneralPaperSourceParameters.prepare k).summarySize+2
  GeneralPaperRoundPrefixViews.profile W m+
    GeneralPaperNativeSelectorPrice.pickProfile model W m lambda k Qv K J height leaves BcWord+
    GeneralPaperNativeSelectorPrice.pickProfile model W m lambda k Qv K J height leaves BrWord+128*W

def arithmeticProfile (m k J depth height leaves : ℕ) : ℕ :=
  GeneralPaperRoundPrefixViews.arithmeticProfile m+
    2*GeneralPaperNativeSelectorPrice.pickArithmeticProfile m k ((GeneralPaperSourceParameters.prepare k).summarySize+2) J depth height leaves+128

theorem work {m k : ℕ} (model : RationalCostModel) (W Qv T : ℕ) (cache : Cache m k)
    (profit : GeneralPaperProfitParameters.Prepared) (hp : profit=GeneralPaperProfitParameters.prepare m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (before : FixedArrayTable m (GeneralPaperEpochSnapshot.Snapshot k)) (Bc Br : ℚ)
    (hT : T=(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).rows) (hWeights : ∑ j,weights.read j=Qv)
    (hLambda : ∀ j,GeneralPaperMeshPrefixInvariant.Good m cache.alphabet.lambda k Qv (before.read j).lambda.cdf)
    (hMu : ∀ j,GeneralPaperMeshPrefixInvariant.Good m cache.alphabet.lambda k Qv (before.read j).mu.cdf) :
    (GeneralPaperChooseRowsExecution.run true (fun x => x) model.rat W cache profit T weights before Bc Br).2≤
      profile model W m cache.alphabet.lambda k Qv profit.grid.size profit.parameters.height profit.parameters.leafCount (rationalWordWidth Bc) (rationalWordWidth Br) ∧
    (GeneralPaperChooseRowsExecution.run false (fun _ => 1) model.rat 1 cache profit T weights before Bc Br).2≤
      arithmeticProfile m k profit.grid.size profit.grid.depth profit.parameters.height profit.parameters.leafCount := by
  have hca : cache.candidate.alphabet=cache.alphabet := by rw [cache.candidate_spec]; rfl
  have hra : cache.response.alphabet=cache.alphabet := by rw [cache.response_spec]; rfl
  have hc := GeneralPaperNativeSelectorPrice.native_work model W Qv T profit cache.candidate weights
    (FixedArrayTable.ofFn (fun j => (before.read j).lambda.cdf)) Bc (by rw [hca]; exact hp) (by rw [hca]; exact hT) hWeights
    (by intro j; rw [hca,FixedArrayTable.read_ofFn]; exact hLambda j)
  have hr := GeneralPaperNativeSelectorPrice.native_work model W Qv T profit cache.response weights
    (FixedArrayTable.ofFn (fun j => (before.read j).mu.cdf)) Br (by rw [hra]; exact hp) (by rw [hra]; exact hT) hWeights
    (by intro j; rw [hra,FixedArrayTable.read_ofFn]; exact hMu j)
  rw [hca] at hc
  rw [hra] at hr
  have hv := GeneralPaperRoundPrefixViews.bit_work W before
  have hva := GeneralPaperRoundPrefixViews.arithmetic_work before
  constructor
  · simp only [GeneralPaperChooseRowsExecution.run,GeneralPaperRoundPrefixViews.data]
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hv hc.1) hr.1) _
  · simp only [GeneralPaperChooseRowsExecution.run,GeneralPaperRoundPrefixViews.data]
    unfold arithmeticProfile
    nlinarith only [hva,hc.2,hr.2]

theorem selected_work {m k : ℕ} (model : RationalCostModel) (W Qv : ℕ) (cache : Cache m k)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hWeights : ∑ j,weights.read j=Qv) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) :
    let current := selected cache Qv weights Bc Br
    (GeneralPaperChooseRowsExecution.run true (fun x => x) model.rat W cache current.profit current.T weights (beforeAt current time) Bc Br).2≤
      profile model W m cache.alphabet.lambda k Qv current.profit.grid.size current.profit.parameters.height current.profit.parameters.leafCount (rationalWordWidth Bc) (rationalWordWidth Br) ∧
    (GeneralPaperChooseRowsExecution.run false (fun _ => 1) model.rat 1 cache current.profit current.T weights (beforeAt current time) Bc Br).2≤
      arithmeticProfile m k current.profit.grid.size current.profit.grid.depth current.profit.parameters.height current.profit.parameters.leafCount :=
  work model W Qv _ cache _ rfl weights _ Bc Br rfl hWeights
    (fun j => GeneralPaperActualMeshPrefixInvariant.selected_good cache Qv weights Bc Br time ht j .lambda)
    (fun j => GeneralPaperActualMeshPrefixInvariant.selected_good cache Qv weights Bc Br time ht j .mu)

end Blotto.GeneralPaperChooseRowsPrice
