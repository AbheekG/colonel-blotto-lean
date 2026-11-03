import Blotto.ImplicitLeafPrefixSampler

/-! Independent bounded block selection and uniform integer rejection realize
the exact expanded weighted leaf prefix up to two geometric bit tails. Error
controls every bounded test and has no numerical-label-cardinality factor. -/

namespace Blotto
open scoped BigOperators Classical
namespace ImplicitLeafCounts

noncomputable def blockIdealMean (C : ℕ) (block : Block) (cutoff : ℤ) (test : Fin (C + 1) → ℝ) : ℝ :=
  if 0 < clippedCount block cutoff then blockMean C block cutoff test else test ⟨0, by omega⟩

theorem blockIdealMean_unit (C : ℕ) (block : Block) (hHi : block.hi ≤ C) (cutoff : ℤ)
    (test : Fin (C + 1) → ℝ) (hTest : ∀ code, 0 ≤ test code ∧ test code ≤ 1) :
    0 ≤ blockIdealMean C block cutoff test ∧ blockIdealMean C block cutoff test ≤ 1 := by
  unfold blockIdealMean
  split
  · exact blockMean_bounds C block cutoff hHi test hTest
  · exact hTest _

theorem blockSample_all_mean_error (C : ℕ) (block : Block) (hHi : block.hi ≤ C) (cutoff : ℤ)
    (attempts : ℕ) (test : Fin (C + 1) → ℝ) (hTest : ∀ code, 0 ≤ test code ∧ test code ≤ 1) :
    |(fairBitKernel (attempts * offsetWidth C)).mean (fun bits => test (blockSample C block hHi cutoff attempts bits)) -
      blockIdealMean C block cutoff test| ≤ 1 / (2 : ℝ) ^ attempts := by
  by_cases hCount : 0 < clippedCount block cutoff
  · simp only [blockIdealMean, hCount, ite_true]
    exact blockSample_mean_error C block hHi cutoff hCount attempts test hTest
  · have hActual : (fairBitKernel (attempts * offsetWidth C)).mean (fun bits => test (blockSample C block hHi cutoff attempts bits)) =
        test ⟨0, by omega⟩ := by
      simp only [blockSample, hCount, dite_false]
      exact (fairBitKernel _).constant _
    rw [hActual]
    simp only [blockIdealMean, hCount, ite_false, sub_self, abs_zero]
    positivity

theorem blockChoice_idealMean (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (cutoff : ℤ) (hc : 0 ≤ cutoff) (test : Fin (C + 1) → ℝ) :
    (blockChoice C blocks hp hw cutoff hc).idealMean (fun index =>
      match index with | some index => blockIdealMean C blocks[index] cutoff test | none => test ⟨0, by omega⟩) =
      blockMixtureMean C blocks cutoff test := by
  unfold RationalFiniteAttempt.idealMean blockChoice
  dsimp only
  have hEach : ∀ index : Fin blocks.length,
      ((blockMass blocks[index] cutoff / prefixMass blocks cutoff : ℚ) : ℝ) * blockIdealMean C blocks[index] cutoff test =
        ((blockMass blocks[index] cutoff : ℝ) * blockMean C blocks[index] cutoff test) / (prefixMass blocks cutoff : ℝ) := by
    intro index
    by_cases hCount : 0 < clippedCount blocks[index] cutoff
    · simp only [blockIdealMean, hCount, ite_true, Rat.cast_div]
      ring
    · have hz : clippedCount blocks[index] cutoff = 0 := by omega
      simp only [blockMass, hz, Nat.cast_zero, zero_mul, zero_div, Rat.cast_zero, zero_mul]
  simp_rw [hEach]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  unfold blockMixtureMean
  rw [← List.ofFn_getElem_eq_map blocks (fun block => (blockMass block cutoff : ℝ) * blockMean C block cutoff test), List.sum_ofFn]
  rw [div_eq_mul_inv]
  rfl

theorem prefixSample_flat_mean (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (cutoff : ℤ) (hc : 0 ≤ cutoff) (K attempts : ℕ) (test : Fin (C + 1) → ℝ) :
    (fairBitKernel (prefixSampleBitBudget C blocks.length K attempts)).mean
      (fun bits => test (prefixSample C blocks hp hw cutoff hc K attempts bits)) =
    (fairBitKernel ((blockChoice C blocks hp hw cutoff hc).bitBudget K)).mean (fun first =>
      (fairBitKernel (attempts * offsetWidth C)).mean (fun rest => test
        (blockSample C blocks[(blockChoice C blocks hp hw cutoff hc).sampleLabel K first]
          (coversFrom_bounds C 0 blocks hp _ (List.getElem_mem _)).2.2 cutoff attempts rest))) :=
  by
    let choice := blockChoice C blocks hp hw cutoff hc
    exact fairBitKernel_blocks (choice.bitBudget K) (attempts * offsetWidth C)
      (fun first rest => test (blockSample C blocks[choice.sampleLabel K first]
        (coversFrom_bounds C 0 blocks hp _ (List.getElem_mem _)).2.2 cutoff attempts rest))

theorem prefixSample_mean_error (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (cutoff : ℤ) (hc : 0 ≤ cutoff) (K attempts : ℕ) (test : Fin (C + 1) → ℝ)
    (hTest : ∀ code, 0 ≤ test code ∧ test code ≤ 1) :
    |(fairBitKernel (prefixSampleBitBudget C blocks.length K attempts)).mean
      (fun bits => test (prefixSample C blocks hp hw cutoff hc K attempts bits)) -
      blockMixtureMean C blocks cutoff test| ≤ 1 / (2 : ℝ) ^ K + 1 / (2 : ℝ) ^ attempts := by
  let choice := blockChoice C blocks hp hw cutoff hc
  let actual : Fin blocks.length → ℝ := fun index =>
    (fairBitKernel (attempts * offsetWidth C)).mean (fun bits => test
      (blockSample C blocks[index] (coversFrom_bounds C 0 blocks hp _ (List.getElem_mem index.isLt)).2.2 cutoff attempts bits))
  let ideal : Fin blocks.length → ℝ := fun index => blockIdealMean C blocks[index] cutoff test
  have hEach : ∀ index, |actual index - ideal index| ≤ 1 / (2 : ℝ) ^ attempts := by
    intro index
    exact blockSample_all_mean_error C _ _ cutoff attempts test hTest
  have hActual : ∀ index, 0 ≤ actual index ∧ actual index ≤ 1 := by
    intro index
    exact (fairBitKernel _).mean_unit _ (fun bits => hTest _)
  have hIdeal : ∀ index, 0 ≤ ideal index ∧ ideal index ≤ 1 := by
    intro index
    exact blockIdealMean_unit C _ (coversFrom_bounds C 0 blocks hp _ (List.getElem_mem index.isLt)).2.2 cutoff test hTest
  let lifted : Option (Fin blocks.length) → ℝ := fun index => match index with
    | some index => ideal index | none => test ⟨0, by omega⟩
  have hCategorical := choice.sampleMean_error K lifted (fun index => by cases index with
    | none => exact hTest _
    | some index => exact hIdeal index)
  have hLift : choice.sampleMean K lifted =
      (fairBitKernel (choice.bitBudget K)).mean (fun bits => ideal (choice.sampleLabel K bits)) := rfl
  have hTarget : choice.idealMean lifted = blockMixtureMean C blocks cutoff test :=
    blockChoice_idealMean C blocks hp hw cutoff hc test
  rw [hLift, hTarget] at hCategorical
  have hCompare : |(fairBitKernel (choice.bitBudget K)).mean (fun bits => actual (choice.sampleLabel K bits)) -
      (fairBitKernel (choice.bitBudget K)).mean (fun bits => ideal (choice.sampleLabel K bits))| ≤ 1 / (2 : ℝ) ^ attempts := by
    exact (fairBitKernel _).contraction _ _ _ (fun bits => hEach _)
  rw [prefixSample_flat_mean]
  change |(fairBitKernel (choice.bitBudget K)).mean (fun bits => actual (choice.sampleLabel K bits)) - blockMixtureMean C blocks cutoff test| ≤ _
  exact (abs_sub_le _ _ _).trans ((add_le_add hCompare hCategorical).trans_eq (add_comm _ _))

theorem prefixSample_weighted_prefix_error (C : ℕ) (blocks : List Block) (hp : Partition C blocks) (hw : Positive blocks)
    (cutoff : ℤ) (hc : 0 ≤ cutoff) (K attempts : ℕ) (test : Fin (C + 1) → ℝ)
    (hTest : ∀ code, 0 ≤ test code ∧ test code ≤ 1) :
    |(fairBitKernel (prefixSampleBitBudget C blocks.length K attempts)).mean
      (fun bits => test (prefixSample C blocks hp hw cutoff hc K attempts bits)) -
      (∑ code : Fin (C + 1), if (code.val : ℤ) ≤ cutoff then (labelMass blocks code.val : ℝ) * test code else 0) /
        (prefixMass blocks cutoff : ℝ)| ≤ 1 / (2 : ℝ) ^ K + 1 / (2 : ℝ) ^ attempts := by
  rw [← blockMixtureMean_exact C blocks hp cutoff test]
  exact prefixSample_mean_error C blocks hp hw cutoff hc K attempts test hTest

end ImplicitLeafCounts
end Blotto
