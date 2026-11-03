import Blotto.ProbabilityWordBitCost
import Blotto.RationalPairLatticeBitCost

/-! Extraction reads the actual probability register of the shared pair
program. Its price equals the canonical probability's integer-field price. -/

namespace Blotto.RationalPairProgram

def wordExtractionBitCost (p : RationalRoundingPair) (registers : Array ℚ) (h : registers = run p) : ℕ :=
  ProbabilityWords.ofRatBitCost (registers.getD 11 0) (by
    rw [h, run_probability]
    exact ⟨p.probability_bounds.1.le, p.probability_bounds.2.le⟩)

theorem wordExtractionBitCost_eq (p : RationalRoundingPair) (registers : Array ℚ) (h : registers = run p) :
    wordExtractionBitCost p registers h =
      ProbabilityWords.ofRatBitCost p.probability ⟨p.probability_bounds.1.le, p.probability_bounds.2.le⟩ := by
  subst registers
  unfold wordExtractionBitCost
  simp only [run_probability]

theorem wordExtractionBitCost_lattice (model : RationalCostModel) (p : RationalRoundingPair)
    (registers : Array ℚ) (hRegisters : registers = run p) {D : ℕ} (hD : 0 < D)
    (h : p.Lattice D) (hUnit : p.lengthI ≤ 1) :
    wordExtractionBitCost p registers hRegisters ≤ 2 * model.rat (3 + 2 * binaryWordWidth D) := by
  rw [wordExtractionBitCost_eq]
  apply ProbabilityWords.ofRatBitCost_bound model
  have hWidth := probability_wordWidth_lattice p hD h hUnit
  omega

end Blotto.RationalPairProgram
