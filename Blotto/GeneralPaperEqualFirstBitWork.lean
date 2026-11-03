import Blotto.GeneralPaperEqualFirstBitOutput

/-! Expected bit work for the actual first-rounding boundary. Source sizes
use the successor bound, while the executed midpoint exponent remains k+5.
No accuracy-encoding length is supplied to a draw. -/
namespace Blotto.GeneralPaperEqualFirstBitWork
open MeasureTheory
open scoped ENNReal
open GeneralPaperEqualFirstRounding
open GeneralPaperEqualBitDrawRates (word log size address)
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem log_step (n k b : ℕ) : log n k b ≤ log n (k+1) b := by
  unfold log
  apply Nat.add_le_add_right
  apply binaryWordWidth_mono
  unfold word size
  omega

theorem address_step (n m k b : ℕ) : address n m k b ≤ address n m (k+1) b := by
  unfold address StoredArrayReferenceList.poolAddressWidth
  apply binaryWordWidth_mono
  have hw : word n k b ≤ word n (k+1) b := by unfold word size; omega
  exact Nat.add_le_add_right (Nat.mul_le_mul (by omega) (Nat.add_le_add_right hw 1)) 1

theorem post_step (model : RationalCostModel) (n m k b : ℕ) :
    GeneralPaperEqualBitPostprocessing.bound model (address n m k b) n m (k+5)
      (GeneralPaperEqualNativeSampler.segmentHeight n (k+1)) b (binaryWordWidth n+k+10) ≤
    GeneralPaperEqualBitPostprocessing.bound model (address n m (k+1) b) n m ((k+1)+5)
      (GeneralPaperEqualNativeSampler.segmentHeight n (k+1)) b (binaryWordWidth n+(k+1)+9) := by
  have hw : GeneralPaperEqualBitPostprocessing.word (GeneralPaperEqualNativeSampler.segmentHeight n (k+1)) b
      (binaryWordWidth n+k+10) (k+5) ≤
      GeneralPaperEqualBitPostprocessing.word (GeneralPaperEqualNativeSampler.segmentHeight n (k+1)) b
        (binaryWordWidth n+(k+1)+9) ((k+1)+5) := by
    unfold GeneralPaperEqualBitPostprocessing.word GeneralPaperEqualBitPostprocessing.height
      GeneralPaperEqualBitPostprocessing.base expressionHeightBudget
    omega
  have hi : GeneralPaperEqualBitPostprocessing.index n m (k+5) ≤
      GeneralPaperEqualBitPostprocessing.index n m ((k+1)+5) := by
    unfold GeneralPaperEqualBitPostprocessing.index GeneralPaperEqualBitMidpoint.indexWord
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (binaryWordWidth_mono (show 2*(k+5)+4 ≤ 2*((k+1)+5)+4 by omega)) 1) _) 1
  unfold GeneralPaperEqualBitPostprocessing.bound
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (model.monotone hw))
    (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
      (Nat.add_le_add_right (Nat.add_le_add (address_step n m k b) hi) 1))

theorem controller {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1)
    (p : GeneralPaperEqualPreparedCache.Prepared
      (GeneralPaperEqualFiniteKernel.terminal (rounded true model W k values v hv) small).partition
      (GeneralPaperEqualFiniteKernel.lottery (rounded true model W k values v hv) small)) :
    2*(GeneralPaperEqualBooleanTrial.bound p+8) ≤ 4294967296*(binaryWordWidth n+k+11) := by
  have h := GeneralPaperEqualBooleanCategoricalContract.small_bound p
    (GeneralPaperEqualNativeCache.compact_count _ small).2
  have hw := GeneralPaperEqualFirstHeights.rejection_range true model W k values v hv small p
  omega

theorem total_bound {n : ℕ} (model : RationalCostModel) (W k b : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1)
    (p : GeneralPaperEqualPreparedCache.Prepared
      (GeneralPaperEqualFiniteKernel.terminal (rounded true model W k values v hv) small).partition
      (GeneralPaperEqualFiniteKernel.lottery (rounded true model W k values v hv) small)) :
    let m := (GeneralPaperEqualFiniteKernel.terminal (rounded true model W k values v hv) small).groups.length
    2*(GeneralPaperEqualBooleanTrial.bound p+8) +
      GeneralPaperEqualBitPostprocessing.bound model (address n m k b) n m (k+5)
        (GeneralPaperEqualNativeSampler.segmentHeight n (k+1)) b (binaryWordWidth n+k+10) +
        16*address n m k b+16 ≤ GeneralPaperEqualFullBitContract.bound model n (k+1) b := by
  dsimp only
  have hc := controller model W k values v hv small p
  have hp := GeneralPaperEqualBitDrawRates.post_bound model n _ (k+1) b
    (GeneralPaperEqualNativeCache.group_count _ small)
  have hPost := post_step model n
    (GeneralPaperEqualFiniteKernel.terminal (rounded true model W k values v hv) small).groups.length k b
  have hA := address_step n
    (GeneralPaperEqualFiniteKernel.terminal (rounded true model W k values v hv) small).groups.length k b
  let R := model.rat (word n (k+1) b)
  let L := log n (k+1) b
  have hL : 1 ≤ L := by dsimp [L, log]; omega
  have hX : binaryWordWidth n+k+11 ≤ R := by
    have hs : binaryWordWidth n+k+11 ≤ size n (k+1) b := by unfold size; omega
    have hw : size n (k+1) b ≤ word n (k+1) b := by unfold word; omega
    exact (hs.trans hw).trans (model.word_le _)
  have hn := Nat.mul_le_mul (show 1 ≤ n+1 by omega) hX
  simp only [Nat.one_mul] at hn
  have hLast := Nat.mul_le_mul_left ((n+1)*R) hL
  simp only [Nat.mul_one] at hLast
  have hPay := Nat.mul_le_mul_left 4294967296 (hn.trans hLast)
  unfold GeneralPaperEqualFullBitContract.bound
  change _ ≤ 8589934592*(n+1)*R*L
  nlinarith only [hc, hp, hPost, hA, hPay]

theorem expected_work {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (a : GeneralPaperEqualSelectedSampler.Sampler (rounded true model W k values v hv) k budget) :
    (∫⁻ trace, ((GeneralPaperEqualSelectedSampler.observed model a trace).work : ℝ≥0∞)
      ∂(GeneralPaperEqualSelectedSampler.traceLaw a : Measure (GeneralPaperEqualBitBranchDraw.Trace a.branch))) ≤
      (GeneralPaperEqualSelectedDraw.workBound model n (k+1) (rationalWordWidth budget) : ℝ≥0∞) := by
  have hA := GeneralPaperEqualSelectedSampler.address_bound a
  have hStep := log_step n k (rationalWordWidth budget)
  cases a with
  | mk branch A hAddress =>
    cases branch with
    | dominant chosen heavy row correct =>
      change A ≤ 2*log n k (rationalWordWidth budget)+1 at hA
      have hp := GeneralPaperEqualSelectedDraw.pure_work_bound A (k+1) budget chosen row correct (by omega)
      have hn : (GeneralPaperEqualBitBranchDraw.copyRow A row).2 ≤
          GeneralPaperEqualSelectedDraw.workBound model n (k+1) (rationalWordWidth budget) :=
        hp.trans (Nat.le_add_left _ _)
      have he : ((GeneralPaperEqualBitBranchDraw.copyRow A row).2 : ℝ≥0∞) ≤
          (GeneralPaperEqualSelectedDraw.workBound model n (k+1) (rationalWordWidth budget) : ℝ≥0∞) := by exact_mod_cast hn
      simp only [GeneralPaperEqualSelectedSampler.observed, GeneralPaperEqualSelectedSampler.traceLaw,
        GeneralPaperEqualBitBranchDraw.observed, GeneralPaperEqualBitBranchDraw.traceLaw, lintegral_const]
      change ((GeneralPaperEqualBitBranchDraw.copyRow A row).2 : ℝ≥0∞)*
        (GeneralPaperEqualBitBranchDraw.unitLaw : Measure Unit) Set.univ ≤ _
      rw [measure_univ, mul_one]
      exact he
    | grouped small sampler hK hB =>
      let p := sampler.prepared
      have hs : 2 ≤ GeneralPaperEqualNativeSampler.segmentHeight n (k+1) := by
        unfold GeneralPaperEqualNativeSampler.segmentHeight GeneralPaperEqualNativeSampler.fieldHeight expressionHeightBudget
        omega
      have hBudget : RationalHeight p.budget (rationalWordWidth budget) := by
        rw [hB]; exact rationalHeight_of_wordWidth budget
      have he := GeneralPaperEqualFullBitDraw.expected_work sampler.categorical model sampler.address hs
        (GeneralPaperEqualFirstHeights.lottery_height true model W k values v hv small) hBudget
        (by omega : 2 ≤ binaryWordWidth n+k+10)
        (GeneralPaperEqualFirstHeights.route_height true model W k values v hv small p)
      apply he.trans
      have hk : p.midpointBits = k+5 := sampler.exponent_correct.trans (congrArg (fun k => k+5) hK)
      have ha : sampler.address = address n
          (GeneralPaperEqualFiniteKernel.terminal (rounded true model W k values v hv) small).groups.length
          k (rationalWordWidth budget) := by
        rw [sampler.address_correct, hK, hB]
      have ht := total_bound model W k (rationalWordWidth budget) values v hv small p
      dsimp only at ht
      rw [← hk, ← ha] at ht
      exact_mod_cast ht.trans (Nat.le_add_right
        (GeneralPaperEqualFullBitContract.bound model n (k+1) (rationalWordWidth budget))
        (GeneralPaperEqualSelectedDraw.pureBound n (k+1) (rationalWordWidth budget)))

end Blotto.GeneralPaperEqualFirstBitWork
