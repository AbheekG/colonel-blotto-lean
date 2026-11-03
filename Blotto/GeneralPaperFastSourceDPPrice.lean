import Blotto.GeneralPaperSizedFastDPPrice

/-! Sum the two actually reached DP-call prices over the complete geometric
source horizon. These are erased component-price sums of native calls, not
an extra execution or a replacement total-source cost/space measurement.
The resource-word aggregation remains balanced inside each call. -/
namespace Blotto.GeneralPaperFastSourceDPPrice
open GeneralPaperFastRationalModel GeneralPaperCatalogueEpochRun GeneralPaperCatalogueEpochCache
open GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
open GeneralPaperCodeAlphabet
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

def pairWork {m k : ℕ} {cache : Cache m k} (model : RationalCostModel) (W : ℕ)
    (current : Run cache) (before : FixedArrayTable m (GeneralPaperEpochSnapshot.Snapshot k)) : ℕ :=
  (GeneralPaperOrderedDPExecution.run true (fun x => x) model.rat W current.profit.grid
    (GeneralPaperOrderedNativeProfitOptimizer.inputTree current.profit current.T current.weights
      (FixedArrayTable.ofFn (fun j => (before.read j).lambda.cdf)) cache.candidate.cached)).2+
  (GeneralPaperOrderedDPExecution.run true (fun x => x) model.rat W current.profit.grid
    (GeneralPaperOrderedNativeProfitOptimizer.inputTree current.profit current.T current.weights
      (FixedArrayTable.ofFn (fun j => (before.read j).mu.cdf)) cache.response.cached)).2

theorem pair_bound {m k : ℕ} {cache : Cache m k} (model : RationalCostModel) (C d W Qv : ℕ)
    (current : Run cache) (before : FixedArrayTable m (GeneralPaperEpochSnapshot.Snapshot k))
    (checked : GeneralPaperSizedFastDPPrice.Both C d model W Qv current before) :
    pairWork model W current before≤2*GeneralPaperSizedFastDPPrice.profile C d W m cache.alphabet.lambda k Qv := by
  have hca : cache.candidate.alphabet=cache.alphabet := by rw [cache.candidate_spec]; rfl
  have hra : cache.response.alphabet=cache.alphabet := by rw [cache.response_spec]; rfl
  have hc := checked.1
  have hr := checked.2
  dsimp only [GeneralPaperSizedFastDPPrice.Prices] at hc hr
  have hc' := hc.trans_eq (show GeneralPaperSizedFastDPPrice.profile C d W m cache.candidate.alphabet.lambda k Qv=
      GeneralPaperSizedFastDPPrice.profile C d W m cache.alphabet.lambda k Qv by rw [hca])
  have hr' := hr.trans_eq (show GeneralPaperSizedFastDPPrice.profile C d W m cache.response.alphabet.lambda k Qv=
      GeneralPaperSizedFastDPPrice.profile C d W m cache.alphabet.lambda k Qv by rw [hra])
  dsimp only [pairWork]
  omega

def epochPair {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch time : ℕ) : ℕ :=
  let shared := prepare a k Qv weights Bc Br
  let current := epochRun shared a k (treesAt shared a k epoch)
  pairWork model W current (beforeAt current time)

theorem epoch_pair_bound {m : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hw : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    epochPair model W k Qv a weights Bc Br epoch time≤2*GeneralPaperSizedFastDPPrice.profile C d W m a.lambda k Qv :=
  pair_bound model C d W Qv _ _ (GeneralPaperSizedFastDPPrice.epoch_both_work hg W k Qv a weights Bc Br hw epoch time ht)

def epochTotal {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch count : ℕ) : ℕ :=
  ∑ time∈Finset.range count,epochPair model W k Qv a weights Bc Br epoch time

theorem epoch_total_bound {m : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hw : ∑ j,weights.read j=Qv) (epoch count : ℕ)
    (hc : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    epochTotal model W k Qv a weights Bc Br epoch count≤count*(2*GeneralPaperSizedFastDPPrice.profile C d W m a.lambda k Qv) := by
  have h := Finset.sum_le_sum (s:=Finset.range count)
    (f:=fun time => epochPair model W k Qv a weights Bc Br epoch time)
    (g:=fun _ => 2*GeneralPaperSizedFastDPPrice.profile C d W m a.lambda k Qv)
    (fun time ht => epoch_pair_bound hg W k Qv a weights Bc Br hw epoch time (by have := Finset.mem_range.mp ht; omega))
  simpa only [epochTotal,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id] using h

def total {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ) : ℕ :=
  ∑ epoch∈Finset.range count,epochTotal model W k Qv a weights Bc Br epoch (GeneralPaperTrajectoryParameters.prepare a.lambda k).period

theorem total_bound {m : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hw : ∑ j,weights.read j=Qv) (count : ℕ) :
    total model W k Qv a weights Bc Br count≤
      2*count*(GeneralPaperTrajectoryParameters.prepare a.lambda k).period*GeneralPaperSizedFastDPPrice.profile C d W m a.lambda k Qv := by
  have h := Finset.sum_le_sum (s:=Finset.range count)
    (f:=fun epoch => epochTotal model W k Qv a weights Bc Br epoch (GeneralPaperTrajectoryParameters.prepare a.lambda k).period)
    (g:=fun _ => (GeneralPaperTrajectoryParameters.prepare a.lambda k).period*(2*GeneralPaperSizedFastDPPrice.profile C d W m a.lambda k Qv))
    (fun epoch _ => epoch_total_bound hg W k Qv a weights Bc Br hw epoch _ (Nat.le_refl _))
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id] at h
  exact h.trans_eq (by ring)

theorem full_horizon {m : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hw : ∑ j,weights.read j=Qv) :
    total model W k Qv a weights Bc Br (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs≤
      2*(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows*GeneralPaperSizedFastDPPrice.profile C d W m a.lambda k Qv := by
  have h := total_bound hg W k Qv a weights Bc Br hw (GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs
  simpa only [GeneralPaperTrajectoryParameters.rows_product,Nat.mul_assoc] using h

end Blotto.GeneralPaperFastSourceDPPrice
