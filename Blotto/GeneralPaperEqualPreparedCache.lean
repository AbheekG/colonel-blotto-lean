import Blotto.GeneralPaperPositiveSegmentCompaction
import Blotto.PaperStoredGroupEmission
import Blotto.GeneralPaperNatPower

/-! Data retained for the paper's equal-budget grouped draw: cached routes,
positive segment tables, integer categorical data, midpoint controls and the
original common budget. Source group/member/formula descriptions occur only
as erased correctness indices, not as additional returned data fields. -/
namespace Blotto.GeneralPaperEqualPreparedCache
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 700000
open GeneralPaperPositiveSegmentCompaction (compact count)
open GeneralPaperEqualCategoricalIntegerData (denominator)

structure Prepared {n m k : ℕ} (G : RationalProportionalGroups n m) (l : RationalSegmentLottery m k) where
  routes : PreparedGroupOutput G
  segments : PreparedSegmentDescriptor (compact l)
  D : ℕ
  D_correct : D = denominator segments.lottery.weight
  counts : FixedArrayTable (count l) ℕ
  counts_correct : ∀ i, counts.read i = GeneralPaperEqualCategoricalIntegerData.count segments.lottery.weight i
  rangeBits : ℕ
  rangeBits_correct : rangeBits = UniformNatRejection.width D
  midpointBits : ℕ
  midpointCount : ℕ
  midpointCount_correct : midpointCount = 2 ^ midpointBits
  budget : ℚ

def prepare {n m k : ℕ} (G : RationalProportionalGroups n m) (l : RationalSegmentLottery m k)
    (K : ℕ) (budget : ℚ) : Prepared G l :=
  let segments := PreparedSegmentDescriptor.prepare (compact l)
  let D := denominator segments.lottery.weight
  let counts := FixedArrayTable.ofFn (GeneralPaperEqualCategoricalIntegerData.count segments.lottery.weight)
  let power := GeneralPaperNatPower.run 2 K
  ⟨PreparedGroupOutput.prepare G, segments, D, rfl, counts, FixedArrayTable.read_ofFn _,
    UniformNatRejection.width D, rfl, K, power.power, (GeneralPaperNatPower.data 2 K).1, budget⟩

theorem prepare_midpoint {n m k : ℕ} (G : RationalProportionalGroups n m) (l : RationalSegmentLottery m k)
    (K : ℕ) (budget : ℚ) :
    (prepare G l K budget).midpointBits = K ∧ (prepare G l K budget).budget = budget := ⟨rfl, rfl⟩

theorem denominator_positive {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) : 0 < p.D := by
  rw [p.D_correct]
  exact GeneralPaperEqualCategoricalIntegerData.denominator_pos _

theorem counts_sum {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) : (∑ i, p.counts.read i) = p.D := by
  simp_rw [p.counts_correct]
  rw [GeneralPaperEqualCategoricalIntegerData.count_sum _ p.segments.lottery.nonnegative p.segments.lottery.mass,
    p.D_correct]

theorem counts_bounded {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (i : Fin (count l)) : p.counts.read i ≤ p.D := by
  rw [p.counts_correct, p.D_correct]
  exact GeneralPaperEqualCategoricalIntegerData.count_le_denominator _ p.segments.lottery.nonnegative
    p.segments.lottery.mass i

def attempt {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (bits : Fin p.rangeBits → Bool) : Option (Fin p.D) :=
  let rank := (balancedBitIndex p.rangeBits bits).val
  if h : rank < p.D then some ⟨rank, h⟩ else none

theorem attempt_eq {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (bits : Fin (UniformNatRejection.width p.D) → Bool) :
    attempt p (fun i => bits (i.cast p.rangeBits_correct)) = UniformNatRejection.attempt p.D bits := by
  have he (N W : ℕ) (hW : W = UniformNatRejection.width N) (bs : Fin (UniformNatRejection.width N) → Bool) :
      (let rank := (balancedBitIndex W (fun i => bs (i.cast hW))).val
       if h : rank < N then some (⟨rank, h⟩ : Fin N) else none) = UniformNatRejection.attempt N bs := by
    subst W
    rfl
  exact he p.D p.rangeBits p.rangeBits_correct bits

def select {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (rank : Fin p.D) : Fin (count l) :=
  GeneralPaperEqualCategoricalSelector.select p.counts.read (rank.cast (counts_sum p).symm)

theorem select_mean {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (f : Fin (count l) → ℝ) :
    (UniformNatRejection.targetKernel p.D (denominator_positive p)).mean (fun r => f (select p r)) =
      ∑ i, (p.segments.weights.read i : ℝ) * f i := by
  change (1 / (p.D : ℝ)) * (∑ r, f (select p r)) = _
  have hs : (∑ r, f (select p r)) = ∑ i, (p.counts.read i : ℝ) * f i := by
    unfold select
    have he := Equiv.sum_comp (finCongr (counts_sum p).symm)
      (fun r => f (GeneralPaperEqualCategoricalSelector.select p.counts.read r))
    exact he.trans (GeneralPaperEqualCategoricalSelector.sum_select p.counts.read f)
  rw [hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he := congrArg (fun q : ℚ => (q : ℝ))
    (GeneralPaperEqualCategoricalIntegerData.count_ratio p.segments.lottery.weight
      p.segments.lottery.nonnegative i)
  rw [← p.D_correct, ← p.counts_correct] at he
  simp only [Rat.cast_div, Rat.cast_natCast] at he
  change (p.counts.read i : ℝ) / p.D = (p.segments.weights.read i : ℝ) at he
  rw [← he]
  ring

def midpoint {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (fresh : Fin p.midpointBits → Bool) : ℚ :=
  ((balancedBitIndex p.midpointBits fresh).val * 2 + 1 : ℚ) / (2 * p.midpointCount : ℕ)

theorem midpoint_eq {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (fresh : Fin p.midpointBits → Bool) :
    midpoint p fresh = dyadicMidpointSample p.midpointBits fresh := by
  unfold midpoint dyadicMidpointSample
  rw [p.midpointCount_correct, Nat.shiftLeft_eq, Nat.one_mul, pow_succ]
  rw [Nat.mul_comm 2 (2 ^ p.midpointBits)]

def groupPoint {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (slot : Fin (count l)) (fresh : Fin p.midpointBits → Bool) : FixedArrayTable m ℚ :=
  let t := midpoint p fresh
  let P := p.segments.left.read slot
  let Q := p.segments.right.read slot
  FixedArrayTable.ofFn (fun j => (1 - t) * P.read j + t * Q.read j)

theorem groupPoint_data {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (slot : Fin (count l)) (fresh : Fin p.midpointBits → Bool) :
    (groupPoint p slot fresh).read = (compact l).point p.midpointBits slot fresh := by
  funext j
  simp only [groupPoint, FixedArrayTable.read_ofFn, midpoint_eq, p.segments.left_correct,
    p.segments.right_correct, RationalSegmentLottery.point, rationalSegmentPoint]

theorem stored_law {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (K : ℕ) : p.segments.lottery.real.dyadicLaw K = l.real.dyadicLaw K := by
  rw [p.segments.lottery_eq]
  exact GeneralPaperPositiveSegmentCompaction.compact_dyadic_law l K

theorem descriptor_cells {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (hm : m ≤ 3) (hk : count l ≤ 7) : p.segments.rationalCells ≤ 49 := by
  rw [PreparedSegmentDescriptor.rationalCells_eq]
  nlinarith only [hm, hk, Nat.mul_le_mul hm hk]

theorem descriptor_payload {n m k s : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (hm : m ≤ 3) (hk : count l ≤ 7) (h : l.HeightAt s) :
    p.segments.payloadBitCost ≤ 49 * (1 + 2 * s) := by
  have he := p.segments.payloadBitCost_bound s (GeneralPaperPositiveSegmentCompaction.compact_height l h)
  have hc : count l + 2 * count l * m ≤ 49 := by nlinarith only [hm, hk, Nat.mul_le_mul hm hk]
  exact he.trans (Nat.mul_le_mul_right _ hc)

theorem denominator_word {n m k s : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (h : l.HeightAt s) : binaryWordWidth p.D ≤ s * count l + 1 := by
  rw [p.D_correct, p.segments.lottery_eq]
  exact GeneralPaperEqualCategoricalIntegerData.denominator_word _
    (GeneralPaperPositiveSegmentCompaction.compact_height l h).1

theorem count_word {n m k s : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (h : l.HeightAt s) (i : Fin (count l)) :
    binaryWordWidth (p.counts.read i) ≤ s * count l + 1 :=
  (binaryWordWidth_mono (counts_bounded p i)).trans (denominator_word p h)

theorem rangeBits_bound {n m k s : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (h : l.HeightAt s) : p.rangeBits ≤ s * count l + 1 := by
  rw [p.rangeBits_correct, p.D_correct, p.segments.lottery_eq]
  exact GeneralPaperEqualCategoricalIntegerData.rejection_width _
    (GeneralPaperPositiveSegmentCompaction.compact_height l h).1

theorem midpointCount_word {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) : binaryWordWidth p.midpointCount = p.midpointBits + 1 := by
  rw [p.midpointCount_correct]
  simp only [binaryWordWidth, Nat.log2_two_pow]

theorem select_eq_rank {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (r : Fin p.D) :
    select p r = GeneralPaperEqualCategoricalSelector.rank p.segments.lottery.weight
      p.segments.lottery.nonnegative p.segments.lottery.mass (r.cast p.D_correct) := by
  have hc : p.counts.read = GeneralPaperEqualCategoricalIntegerData.count p.segments.lottery.weight :=
    funext p.counts_correct
  have he (c c' : Fin (count l) → ℕ) (hh : c = c')
      (a : Fin (∑ i, c i)) (b : Fin (∑ i, c' i)) (hab : a.val = b.val) :
      GeneralPaperEqualCategoricalSelector.select c a = GeneralPaperEqualCategoricalSelector.select c' b := by
    subst c'
    congr 1
    exact Fin.ext hab
  unfold select GeneralPaperEqualCategoricalSelector.rank
  exact he _ _ hc _ _ rfl

theorem cached_select_mean {n m k : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m k}
    (p : Prepared G l) (f : Fin (count l) → ℝ) :
    (UniformNatRejection.targetKernel p.D (denominator_positive p)).mean (fun r => f (select p r)) =
      ∑ i, ((compact l).weight i : ℝ) * f i := by
  rw [select_mean]
  apply Finset.sum_congr rfl
  intro i _
  rw [p.segments.weight_correct]

end Blotto.GeneralPaperEqualPreparedCache
