import Blotto.UniformNatRejection
import Blotto.ImplicitLeafBlockMixture
import Blotto.NativePreparedTrainingHistory
import Blotto.RationalFiniteAttemptMean

/-! Bounded conditional leaf draws choose a stored clipped block and then a
uniform original code offset. Both stages consume independent fresh blocks;
zero clipped masses return the feasible zero fallback. No label-universe list
is constructed in sampling. The exact two-stage law is proved separately. -/

namespace Blotto
open scoped BigOperators Classical
namespace ImplicitLeafCounts

theorem partition_blocks_nonempty (C : ℕ) (blocks : List Block) (hp : Partition C blocks) : 0 < blocks.length := by
  cases blocks with
  | nil => change 0 = C + 1 at hp; omega
  | cons block rest => simp

theorem blockMass_sum (blocks : List Block) (cutoff : ℤ) :
    (∑ index : Fin blocks.length, blockMass blocks[index] cutoff) = prefixMass blocks cutoff := by
  induction blocks with
  | nil => simp [prefixMass]
  | cons block rest ih => simpa [Fin.sum_univ_succ, prefixMass] using congrArg (fun mass => blockMass block cutoff + mass) ih

def blockChoice (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (cutoff : ℤ) (hc : 0 ≤ cutoff) : RationalFiniteAttempt blocks.length blocks.length where
  weight := fun index => blockMass blocks[index] cutoff / prefixMass blocks cutoff
  nonnegative := by
    intro index
    exact div_nonneg (blockMass_nonnegative _ _ (hw _ (List.getElem_mem index.isLt)).le)
      (partition_prefixMass_positive C blocks hp hw cutoff hc).le
  sum_one := by
    have hs := blockMass_sum blocks cutoff
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, hs, mul_inv_cancel₀ (ne_of_gt (partition_prefixMass_positive C blocks hp hw cutoff hc))]
  decode := some
  fallbackLabel := ⟨0, partition_blocks_nonempty C blocks hp⟩

def offsetWidth (C : ℕ) : ℕ := UniformNatRejection.width (C + 1)

theorem clippedCount_bound (C : ℕ) (block : Block) (hHi : block.hi ≤ C) (cutoff : ℤ) : clippedCount block cutoff ≤ C + 1 := by
  unfold clippedCount
  omega

theorem uniform_width_mono {first last : ℕ} (hFirst : 0 < first) (hLast : first ≤ last) :
    UniformNatRejection.width first ≤ UniformNatRejection.width last :=
  widthRatioPrecision_minimal first 1 _ hFirst (by decide)
    (by simpa only [one_mul] using hLast.trans (UniformNatRejection.width_upper last))

def blockSample (C : ℕ) (block : Block) (hHi : block.hi ≤ C) (cutoff : ℤ) (attempts : ℕ)
    (bits : Fin (attempts * offsetWidth C) → Bool) : Fin (C + 1) :=
  if hCount : 0 < clippedCount block cutoff then
    let hWidth := uniform_width_mono hCount (clippedCount_bound C block hHi cutoff)
    let seed : Fin (attempts * UniformNatRejection.width (clippedCount block cutoff)) → Bool :=
      fun index => bits ⟨index.val, Nat.lt_of_lt_of_le index.isLt (Nat.mul_le_mul_left attempts hWidth)⟩
    offsetLabel C block cutoff hHi (UniformNatRejection.sample (clippedCount block cutoff) hCount attempts seed)
  else ⟨0, by omega⟩

def prefixSampleBitBudget (C B K attempts : ℕ) : ℕ := 3 * (B - 1 + K) + attempts * offsetWidth C

def prefixSample (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (cutoff : ℤ) (hc : 0 ≤ cutoff) (K attempts : ℕ)
    (bits : Fin (prefixSampleBitBudget C blocks.length K attempts) → Bool) : Fin (C + 1) :=
  let choice := blockChoice C blocks hp hw cutoff hc
  let blockIndex := choice.sampleLabel K (firstBitBlock (choice.bitBudget K) (attempts * offsetWidth C) bits)
  let block := blocks[blockIndex]
  blockSample C block (coversFrom_bounds C 0 blocks hp block (List.getElem_mem blockIndex.isLt)).2.2 cutoff attempts
    (secondBitBlock (choice.bitBudget K) (attempts * offsetWidth C) bits)

theorem blockSample_feasible (C : ℕ) (block : Block) (hHi : block.hi ≤ C) (cutoff : ℤ) (hc : 0 ≤ cutoff)
    (attempts : ℕ) (bits : Fin (attempts * offsetWidth C) → Bool) :
    ((blockSample C block hHi cutoff attempts bits).val : ℤ) ≤ cutoff := by
  unfold blockSample
  split
  · rename_i hCount
    let hWidth := uniform_width_mono hCount (clippedCount_bound C block hHi cutoff)
    let seed : Fin (attempts * UniformNatRejection.width (clippedCount block cutoff)) → Bool :=
      fun index => bits ⟨index.val, Nat.lt_of_lt_of_le index.isLt (Nat.mul_le_mul_left attempts hWidth)⟩
    have hm := offsetLabel_mem C block cutoff hHi
      (UniformNatRejection.sample (clippedCount block cutoff) hCount attempts seed)
    simp only [blockLabels, Finset.mem_filter, Finset.mem_univ, true_and] at hm
    exact hm.2
  · exact hc

theorem prefixSample_feasible (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (cutoff : ℤ) (hc : 0 ≤ cutoff) (K attempts : ℕ)
    (bits : Fin (prefixSampleBitBudget C blocks.length K attempts) → Bool) :
    ((prefixSample C blocks hp hw cutoff hc K attempts bits).val : ℤ) ≤ cutoff :=
  blockSample_feasible C _ _ cutoff hc attempts _

theorem blockSample_mean_error (C : ℕ) (block : Block) (hHi : block.hi ≤ C) (cutoff : ℤ)
    (hCount : 0 < clippedCount block cutoff) (attempts : ℕ) (test : Fin (C + 1) → ℝ)
    (hTest : ∀ code, 0 ≤ test code ∧ test code ≤ 1) :
    |(fairBitKernel (attempts * offsetWidth C)).mean (fun bits => test (blockSample C block hHi cutoff attempts bits)) -
      blockMean C block cutoff test| ≤ 1 / (2 : ℝ) ^ attempts := by
  unfold blockSample
  simp only [hCount, dite_true]
  have hWidth := uniform_width_mono hCount (clippedCount_bound C block hHi cutoff)
  have hPrefix := fairBitKernel_prefix_mean (attempts * UniformNatRejection.width (clippedCount block cutoff))
    (attempts * offsetWidth C) (Nat.mul_le_mul_left attempts hWidth)
    (fun bits => test (offsetLabel C block cutoff hHi (UniformNatRejection.sample (clippedCount block cutoff) hCount attempts bits)))
  rw [hPrefix]
  have he := UniformNatRejection.sample_mean_error (clippedCount block cutoff) hCount attempts
    (fun offset => test (offsetLabel C block cutoff hHi offset)) (fun offset => hTest _)
  have hIdeal : (UniformNatRejection.targetKernel (clippedCount block cutoff) hCount).mean
      (fun offset => test (offsetLabel C block cutoff hHi offset)) = blockMean C block cutoff test := by
    change (1 / (clippedCount block cutoff : ℝ)) * (∑ offset, test (offsetLabel C block cutoff hHi offset)) = _
    rw [one_div, mul_comm, ← div_eq_mul_inv]
    exact uniform_offsets_mean C block cutoff hHi test
  rw [hIdeal] at he
  exact he

end ImplicitLeafCounts
end Blotto
