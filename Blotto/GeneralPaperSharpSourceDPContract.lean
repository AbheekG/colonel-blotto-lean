import Blotto.GeneralPaperSharpDPSourceRate
import Blotto.GeneralPaperFastSourceDPPrice

/-! The two native DP calls over every permitted source prefix satisfy the
paper's second fast-bit source term. These are erased component-price sums,
not a replacement for the complete source controller or a space bound. -/
namespace Blotto.GeneralPaperSharpSourceDPContract
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperNativeSourceRates
open GeneralPaperSharpDPSourceRate GeneralPaperFastRationalModel
open GeneralPaperCatalogueEpochRun GeneralPaperCatalogueEpochCache
open GeneralPaperInitializerPreparedPoint
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem pair_bound {m k : ℕ} {cache : Cache m k} {model : RationalCostModel} {C d : ℕ}
    (hg : Growth model C d) (W Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hw : ∑ j,weights.read j=Qv) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) :
    GeneralPaperFastSourceDPPrice.pairWork model W (selected cache Qv weights Bc Br)
      (beforeAt (selected cache Qv weights Bc Br) time)≤
      2*GeneralPaperFastOrderedDPPrice.fieldProfile C d W m cache.alphabet.lambda k Qv
        ((GeneralPaperSourceParameters.prepare k).summarySize+2)
        (GeneralPaperProfitParameters.prepare m cache.alphabet.lambda k Qv).grid.size (cache.alphabet.lambda+1) := by
  have checked := GeneralPaperActualFastOrderedDPPrice.both_work hg W Qv cache weights Bc Br hw time ht
  have hca : cache.candidate.alphabet=cache.alphabet := by rw [cache.candidate_spec]; rfl
  have hra : cache.response.alphabet=cache.alphabet := by rw [cache.response_spec]; rfl
  have hc := checked.1
  have hr := checked.2
  dsimp only [GeneralPaperActualFastOrderedDPPrice.Prices] at hc hr
  rw [hca] at hc
  rw [hra] at hr
  dsimp only [GeneralPaperFastSourceDPPrice.pairWork,selected] at hc hr ⊢
  omega

theorem epoch_pair_bound {m : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W k Qv : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hw : ∑ j,weights.read j=Qv) (epoch time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).period) :
    GeneralPaperFastSourceDPPrice.epochPair model W k Qv a weights Bc Br epoch time≤
      2*GeneralPaperFastOrderedDPPrice.fieldProfile C d W m a.lambda k Qv
        ((GeneralPaperSourceParameters.prepare k).summarySize+2)
        (GeneralPaperProfitParameters.prepare m a.lambda k Qv).grid.size (a.lambda+1) := by
  unfold GeneralPaperFastSourceDPPrice.epochPair
  dsimp only
  rw [GeneralPaperCatalogueShared.epochRun_selected]
  exact pair_bound hg W Qv weights Bc Br hw time ht

theorem total_bound {m : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W k Qv : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hw : ∑ j,weights.read j=Qv) (count : ℕ) :
    GeneralPaperFastSourceDPPrice.total model W k Qv a weights Bc Br count≤
      2*count*(GeneralPaperTrajectoryParameters.prepare a.lambda k).period*
        GeneralPaperFastOrderedDPPrice.fieldProfile C d W m a.lambda k Qv
          ((GeneralPaperSourceParameters.prepare k).summarySize+2)
          (GeneralPaperProfitParameters.prepare m a.lambda k Qv).grid.size (a.lambda+1) := by
  unfold GeneralPaperFastSourceDPPrice.total GeneralPaperFastSourceDPPrice.epochTotal
  calc
    _≤∑ epoch∈Finset.range count,∑ time∈Finset.range (GeneralPaperTrajectoryParameters.prepare a.lambda k).period,
      2*GeneralPaperFastOrderedDPPrice.fieldProfile C d W m a.lambda k Qv
        ((GeneralPaperSourceParameters.prepare k).summarySize+2)
        (GeneralPaperProfitParameters.prepare m a.lambda k Qv).grid.size (a.lambda+1) := by
      apply Finset.sum_le_sum
      intro epoch _
      apply Finset.sum_le_sum
      intro time ht
      exact epoch_pair_bound hg W k Qv a weights Bc Br hw epoch time (by have := Finset.mem_range.mp ht; omega)
    _=_ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id]; ring

theorem rows_rate : Soft (fun x => symbols x*(accuracy x)^2)
    (fun x => (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows) := by
  apply bounded (2^48)
  intro x
  have he := (GeneralPaperTrajectoryParameters.epochs_upper (alphabet x).lambda x.k).le
  have hsize : (alphabet x).lambda+2≤2*symbols x := by unfold symbols; omega
  have he' := he.trans (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right (2^(35+x.k)) hsize))
  have hprod := Nat.mul_le_mul_right (2^(11+x.k)) he'
  rw [GeneralPaperTrajectoryParameters.rows_product,GeneralPaperTrajectoryParameters.period_power]
  apply hprod.trans_eq
  dsimp only [accuracy]
  rw [pow_add,pow_add]
  norm_num only [show (2:ℕ)^35=34359738368 by decide,show (2:ℕ)^11=2048 by decide,
    show (2:ℕ)^48=281474976710656 by decide]
  ring

def totalRate (x : Input) : ℕ := fields x*(symbols x)^2*(accuracy x)^4

noncomputable def cap (C d : ℕ) (x : Input) : ℕ :=
  2*(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows*actualProfile C d x

theorem cap_rate (C d : ℕ) : Soft totalRate (cap C d) := by
  have h := mul (poly_mul_rate (poly_constant 2) rows_rate) (actual_profile_rate C d)
  apply rate_mono h
  intro x
  dsimp only [totalRate,callRate,resourceRate]
  exact le_of_eq (by ring)

theorem native_prefix_cap {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (x : Input) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs) :
    GeneralPaperFastSourceDPPrice.total model (GeneralPaperLogarithmicSourceReference.width C d x)
      x.k x.Qv (alphabet x) x.weights
      (ownBudget x.m x.k (x.b:ℝ) x.reciprocal) (opposingBudget x.m x.k (x.b:ℝ) x.reciprocal) count≤cap C d x := by
  have h := total_bound hg (GeneralPaperLogarithmicSourceReference.width C d x) x.k x.Qv (alphabet x) x.weights
    (ownBudget x.m x.k (x.b:ℝ) x.reciprocal) (opposingBudget x.m x.k (x.b:ℝ) x.reciprocal) x.weight_sum count
  apply h.trans
  change 2*count*(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).period*actualProfile C d x≤cap C d x
  apply (Nat.mul_le_mul_right (actualProfile C d x)
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 he))).trans_eq
  unfold cap
  rw [GeneralPaperTrajectoryParameters.rows_product]
  ring

theorem sharp_prefix_bound {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d) :
    ∃ A e : ℕ,∀ (x : Input) (count : ℕ),
      count≤(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs →
      GeneralPaperFastSourceDPPrice.total model (GeneralPaperLogarithmicSourceReference.width C d x)
        x.k x.Qv (alphabet x) x.weights
        (ownBudget x.m x.k (x.b:ℝ) x.reciprocal) (opposingBudget x.m x.k (x.b:ℝ) x.reciprocal) count≤
        A*(x.m+1)*((alphabet x).lambda+1)^2*2^(4*x.k)*(logSize x)^e := by
  rcases cap_rate C d with ⟨A,e,hA⟩
  refine ⟨A,e,fun x count he => (native_prefix_cap hg x count he).trans ((hA x).trans_eq ?_)⟩
  dsimp only [totalRate,fields,symbols,accuracy]
  rw [←pow_mul]
  congr 1
  ring

theorem sharp_nonempty_prefix_bound {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d) :
    ∃ A e : ℕ,∀ (x : Input) (count : ℕ),1≤x.m →
      count≤(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs →
      GeneralPaperFastSourceDPPrice.total model (GeneralPaperLogarithmicSourceReference.width C d x)
        x.k x.Qv (alphabet x) x.weights
        (ownBudget x.m x.k (x.b:ℝ) x.reciprocal) (opposingBudget x.m x.k (x.b:ℝ) x.reciprocal) count≤
        A*x.m*(alphabet x).lambda^2*2^(4*x.k)*(logSize x)^e := by
  rcases sharp_prefix_bound hg with ⟨A,e,hA⟩
  refine ⟨8*A,e,?_⟩
  intro x count hm he
  have hl := GeneralPaperSourceAlphabetLower.fields_le_lambda x.m x.k
  change x.m≤(alphabet x).lambda at hl
  have hm' : x.m+1≤2*x.m := by omega
  have hl' : (alphabet x).lambda+1≤2*(alphabet x).lambda := by omega
  have hprod := Nat.mul_le_mul_right (2^(4*x.k)*(logSize x)^e)
    (Nat.mul_le_mul (Nat.mul_le_mul_left A hm') (Nat.pow_le_pow_left hl' 2))
  apply (hA x count he).trans
  simpa only [Nat.mul_assoc] using hprod.trans_eq (by ring)

end Blotto.GeneralPaperSharpSourceDPContract
