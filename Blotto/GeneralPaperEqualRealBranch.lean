import Blotto.GeneralPaperEqualRealBoundaryScan

/-! The two actual equal-budget return variants have one mathematical
contract. Dominant returns own a constructed full-budget row; grouped
returns own the smaller real cache. Proof fields erase from both variants. -/
namespace Blotto.GeneralPaperEqualRealBranch
open MeasureTheory
open GeneralPaperEqualFiniteKernel (terminal lottery)
open GeneralPaperEqualRealCache (Cache view)
set_option autoImplicit false
set_option maxHeartbeats 1800000

inductive Prepared {n : ℕ} (v : RationalFieldSelector n) (k : ℕ) (budget : ℚ) where
  | dominant (chosen : Fin n) (heavy : (1 / 2 : ℚ) ≤ v.weight chosen)
      (row : RationalResourceArray n)
      (correct : row.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen)
  | grouped (small : ∀ j, 2 * v.weight j ≤ 1)
      (cache : Cache (terminal v small).partition (lottery v small))
      (precision : cache.midpointBits = k + 5) (originalBudget : cache.budget = budget)

noncomputable def outputLaw {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} : Prepared v k budget → Mixed n
  | .dominant _ _ row _ => PureBoundaryEquilibria.pointLaw row.realAllocation
  | .grouped _ cache _ _ => GeneralPaperEqualRealCacheDraw.outputLaw cache

theorem grouped_law {n : ℕ} (v : RationalFieldSelector n) (k : ℕ) (budget : ℚ)
    (small : ∀ j, 2 * v.weight j ≤ 1) (cache : Cache (terminal v small).partition (lottery v small))
    (hK : cache.midpointBits = k + 5) (hB : cache.budget = budget) :
    outputLaw (.grouped small cache hK hB) = scaleLaw (budget : ℝ) (GeneralPaperEqualFiniteKernel.law v small k) := by
  rw [outputLaw, GeneralPaperEqualRealCacheDraw.outputLaw_eq, GeneralPaperEqualRealDraw.outputLaw_eq]
  dsimp only [GeneralPaperEqualCachedTraceLaw.target, view]
  rw [hK, hB, GeneralPaperPositiveSegmentCompaction.compact_dyadic_law]
  rfl

theorem rounded_regret {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (p : Prepared v k budget) (hB : 0 < budget) :
    Supported (budget : ℝ) (outputLaw p) ∧
      regret v.values (budget : ℝ) (outputLaw p) (outputLaw p) ≤ (1 / (2 : ℝ) ^ k) / 32 := by
  have hBr : (0 : ℝ) < budget := by exact_mod_cast hB
  cases p with
  | dominant chosen heavy row correct =>
    have hh : (1 / 2 : ℝ) ≤ v.values.weight chosen := by
      change (1 / 2 : ℝ) ≤ (v.weight chosen : ℝ)
      have hh' : (((1 / 2 : ℚ) : ℝ)) ≤ (v.weight chosen : ℝ) := by exact_mod_cast heavy
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hh'
    have h := PureBoundaryEquilibria.dominant_vertex_equilibrium v.values (budget : ℝ) hBr.le chosen hh
    simp only [outputLaw, correct]
    exact ⟨h.1, h.2.le.trans (by positivity)⟩
  | grouped small cache hK hBudget =>
    rw [grouped_law]
    have h := GeneralPaperEqualFiniteKernel.regrets v small k
    refine ⟨?_, ?_⟩
    · simpa only [mul_one] using scaleLaw_supported hBr.le _ h.1
    · have hs := regret_scale v.values hBr 1 (GeneralPaperEqualFiniteKernel.law v small k) (GeneralPaperEqualFiniteKernel.law v small k)
      rw [mul_one] at hs
      exact hs.le.trans h.2

theorem expected_half {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (p : Prepared v k budget) (original : Values n) : expected original (outputLaw p) (outputLaw p) = 1 / 2 := by
  have h := expected_constant_sum original (outputLaw p) (outputLaw p)
  linarith only [h]

def prepare {n : ℕ} (v : RationalFieldSelector n) (k : ℕ) (budget : ℚ)
    (lengths : FixedArrayTable n ℚ) (hL : ∀ j, lengths.read j = 2 * v.weight j) : Prepared v k budget × ℕ :=
  let scanned := GeneralPaperEqualRealBoundaryScan.run lengths
  match h : scanned.1 with
  | some chosen =>
    let heavy := GeneralPaperEqualRealBoundaryScan.some_heavy lengths v hL chosen h
    let row := GeneralPaperEqualRealBoundaryScan.vertex budget chosen
    (.dominant chosen heavy row.1 (GeneralPaperEqualRealBoundaryScan.vertex_data budget chosen), scanned.2 + row.2 + 64)
  | none =>
    let small := GeneralPaperEqualRealBoundaryScan.none_small lengths v hL h
    let made := GeneralPaperEqualRealPreparation.make v small lengths hL k budget
    (.grouped small made.1 rfl rfl, scanned.2 + made.2 + 64)

theorem prepare_work {n : ℕ} (v : RationalFieldSelector n) (k : ℕ) (budget : ℚ)
    (lengths : FixedArrayTable n ℚ) (hL : ∀ j, lengths.read j = 2 * v.weight j) :
    (prepare v k budget lengths hL).2 ≤
      1024 * (n + 1) + 64 * (binaryWordWidth (k + 5) + 1) ^ 2 + 2150064 := by
  have hs := GeneralPaperEqualRealBoundaryScan.run_work lengths
  unfold prepare
  dsimp only
  split
  · rename_i chosen h
    have hv := GeneralPaperEqualRealBoundaryScan.vertex_work budget chosen
    omega
  · rename_i h
    have hm := GeneralPaperEqualRealPreparation.make_work v
      (GeneralPaperEqualRealBoundaryScan.none_small lengths v hL h) lengths hL k budget
    omega

end Blotto.GeneralPaperEqualRealBranch
