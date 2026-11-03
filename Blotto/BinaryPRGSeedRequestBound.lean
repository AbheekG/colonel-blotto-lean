import Blotto.BinaryPRGSeedBlockOutput

/-! Accepted native requests internally derive their dimension, precision,
flat-seed count and seed-block preparation envelope from incoming frame length.
No declared-count/precision/seed-size oracle or natural primitive envelope is
supplied. Small scalar/backend/ownership/physical/whole-model costs remain open. -/

namespace Blotto.BinaryPRGSeedRequestBound
open RationalLottoResourceSystem BinaryPRGAccuracyRulerRequest

theorem read_dimension_bound (frame : List Bool) (parsed : (Σ n, Request n) × List Bool)
    (h : (read frame).1 = some parsed) : parsed.1.1 ≤ frame.length := by
  unfold BinaryPRGAccuracyRulerRequest.read at h
  dsimp only at h
  split at h
  · cases h
  · rename_i game hg
    have hOld : (BinaryPRGNormalizedFrameWork.read frame).1 = some game :=
      (BinaryPRGNormalizedFrameWork.read_state frame).trans ((BinaryPRGStoredDimensionFrame.read_state frame).symm.trans hg)
    have hn := (BinaryDecodedInputLength.parsed_sizes frame game hOld).1
    split at h
    · cases h
    · obtain ⟨accuracy,ha,hOut⟩ := Option.map_eq_some_iff.mp h
      subst parsed
      exact hn

def seedCountBound (length : ℕ) : ℕ := 8 * length + 3025

theorem read_seedCount_bound (frame : List Bool) (parsed : (Σ n, Request n) × List Bool)
    (h : (read frame).1 = some parsed) : sampleBitBudget parsed.1.1 parsed.1.2.request.precision ≤ seedCountBound frame.length := by
  have hn := read_dimension_bound frame parsed h
  have hk := read_precision_bound frame parsed h
  rw [sampleBitBudget_eq]
  unfold seedCountBound
  omega

def preparationBound (length : ℕ) : ℕ := BinaryPRGSeedBlocks.bound (seedCountBound length)

theorem read_seed_preparation_bound (frame seed : List Bool) (parsed : (Σ n, Request n) × List Bool)
    (h : (read frame).1 = some parsed) :
    (BinaryPRGSeedBlocks.read parsed.1.1 parsed.1.2.request.precision seed).2.recorded ≤ preparationBound frame.length :=
  (BinaryPRGSeedBlocks.read_bound _ _ seed).trans (BinaryPRGSeedBlocks.bound_mono (read_seedCount_bound frame parsed h))

theorem preparationBound_square (length : ℕ) : preparationBound length ≤ (8 * length + 3030) ^ 2 :=
  BinaryPRGSeedBlocks.bound_square (seedCountBound length)

end Blotto.BinaryPRGSeedRequestBound
