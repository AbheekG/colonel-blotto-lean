import Blotto.GeneralPaperSelectedLocalEpochExecution

/-! Complete local epoch prices: eight initial arrays, reached rounds and
one bounded push per retained row. Period is a retained capacity parameter. -/
namespace Blotto.GeneralPaperLocalEpochPrice
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueEpochRun
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def profile (model : RationalCostModel) (W m lambda k Qv J height leaves BcWord BrWord count : ℕ) : ℕ :=
  let period := (GeneralPaperTrajectoryParameters.prepare lambda k).period
  GeneralPaperEpochInitialFamilyPrice.profile model.rat W m k+
    (count*(GeneralPaperRoundPrice.profile model W m lambda k Qv J height leaves BcWord BrWord+256*arrayWord W (period+2))+
      256*arrayWord W (period+2))+128*W

def arithmeticProfile (m lambda k Qv J depth height leaves count : ℕ) : ℕ :=
  GeneralPaperEpochInitialFamilyPrice.arithmeticProfile m k+
    (count*(GeneralPaperRoundPrice.arithmeticProfile m lambda k Qv J depth height leaves+256)+256)+128

theorem capacity_word (W capacity : ℕ) : 1+binaryWordWidth (capacity+1)≤arrayWord W (capacity+2) := by
  have h := binaryWordWidth_mono (show capacity+1≤(capacity+2)+1 by omega)
  unfold arrayWord
  omega

theorem work {m k : ℕ} (model : RationalCostModel) (W Qv : ℕ) (cache : Cache m k)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (hCodes : GeneralPaperCatalogueEpochMetadata.CodesValid cache) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hWeights : ∑ j,weights.read j=Qv) (count : ℕ) (ht : count≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) :
    let current := selected cache Qv weights Bc Br
    let period := (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period
    (GeneralPaperLocalEpochExecution.execute true (fun x => x) model.rat W c cache current.profit current.T weights Bc Br period count).2≤
      profile model W m cache.alphabet.lambda k Qv current.profit.grid.size current.profit.parameters.height current.profit.parameters.leafCount
        (rationalWordWidth Bc) (rationalWordWidth Br) count ∧
    (GeneralPaperLocalEpochExecution.execute false (fun _ => 1) model.rat 1 c cache current.profit current.T weights Bc Br period count).2≤
      arithmeticProfile m cache.alphabet.lambda k Qv current.profit.grid.size current.profit.grid.depth current.profit.parameters.height current.profit.parameters.leafCount count := by
  let current := selected cache Qv weights Bc Br
  let period := (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period
  have hbRounds : ∀ time<count, (GeneralPaperRoundExecution.run true (fun x => x) model.rat W c cache current.profit current.T weights Bc Br
      (GeneralPaperLocalEpochExecution.run true (fun x => x) model.rat W c cache current.profit current.T weights Bc Br
        (GeneralPaperEpochInitialFamilyPrice.run true (fun x => x) model.rat W cache).1 period time).1.1).2≤
      GeneralPaperRoundPrice.profile model W m cache.alphabet.lambda k Qv current.profit.grid.size current.profit.parameters.height current.profit.parameters.leafCount (rationalWordWidth Bc) (rationalWordWidth Br) := by
    intro time hTime
    have hs := GeneralPaperSelectedLocalEpochExecution.prefix_state true (fun x => x) model.rat W Qv cache c hc weights Bc Br period time
    change (GeneralPaperLocalEpochExecution.run true (fun x => x) model.rat W c cache current.profit current.T weights Bc Br
      (GeneralPaperEpochInitialFamilyPrice.run true (fun x => x) model.rat W cache).1 period time).1.1=stateAt current time at hs
    rw [hs]
    exact (GeneralPaperRoundPrice.work model W Qv cache c hc hCodes weights Bc Br hWeights time (by omega)).1
  have huRounds : ∀ time<count, (GeneralPaperRoundExecution.run false (fun _ => 1) model.rat 1 c cache current.profit current.T weights Bc Br
      (GeneralPaperLocalEpochExecution.run false (fun _ => 1) model.rat 1 c cache current.profit current.T weights Bc Br
        (GeneralPaperEpochInitialFamilyPrice.run false (fun _ => 1) (fun _ => 1) 1 cache).1 period time).1.1).2≤
      GeneralPaperRoundPrice.arithmeticProfile m cache.alphabet.lambda k Qv current.profit.grid.size current.profit.grid.depth current.profit.parameters.height current.profit.parameters.leafCount := by
    intro time hTime
    have hs := GeneralPaperSelectedLocalEpochExecution.prefix_state false (fun _ => 1) model.rat 1 Qv cache c hc weights Bc Br period time
    change (GeneralPaperLocalEpochExecution.run false (fun _ => 1) model.rat 1 c cache current.profit current.T weights Bc Br
      (GeneralPaperEpochInitialFamilyPrice.run false (fun _ => 1) (fun _ => 1) 1 cache).1 period time).1.1=stateAt current time at hs
    rw [hs]
    exact (GeneralPaperRoundPrice.work model W Qv cache c hc hCodes weights Bc Br hWeights time (by omega)).2
  have hb := GeneralPaperLocalEpochLoopPrice.work true (fun x => x) model.rat (fun _ _ h => h) W _ c cache current.profit current.T weights Bc Br
    (GeneralPaperEpochInitialFamilyPrice.run true (fun x => x) model.rat W cache).1 period count
    (GeneralPaperSummaryArrayControls.array_word_positive W (period+2)) (capacity_word W period) ht hbRounds
  have hu := GeneralPaperLocalEpochLoopPrice.work false (fun _ => 1) model.rat (fun _ _ _ => Nat.le_refl _) 1 _ c cache current.profit current.T weights Bc Br
    (GeneralPaperEpochInitialFamilyPrice.run false (fun _ => 1) (fun _ => 1) 1 cache).1 period count
    (Nat.le_refl _) (Nat.le_refl _) ht huRounds
  exact ⟨Nat.add_le_add_right (Nat.add_le_add (GeneralPaperEpochInitialFamilyPrice.bit_work model.rat W cache) hb) _,
    Nat.add_le_add_right (Nat.add_le_add (GeneralPaperEpochInitialFamilyPrice.arithmetic_work cache) hu) _⟩

end Blotto.GeneralPaperLocalEpochPrice
