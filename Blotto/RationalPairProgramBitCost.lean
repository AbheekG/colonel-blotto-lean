import Blotto.RationalArithmeticBitCost
import Blotto.RationalPairProgramHeight
import Blotto.RationalUnitLatticeHeight

/-! Operand and conservative scratch-copy prices for the actual seven
pair-preparation instructions, initial fields and endpoint/probability reads.
Fixed-depth register bounds cover every prefix. A common lattice supplies a
bound independent of the resource-rounding depth and minimum positive gap. -/

namespace Blotto.RationalPairProgram

theorem final_wordBounds {p : RationalRoundingPair} {s : ℕ} (h : p.FieldsHeight s) (hs : 2 ≤ s) :
    RationalArithmeticProgram.WordBounds (run p) (32 * s + 31) := by
  intro j
  by_cases hj : j < 12
  · exact registers_wordWidth h hs ⟨j, hj⟩
  · have hZero : rationalWordWidth (0 : ℚ) = 3 := by decide
    have hWidth : rationalWordWidth (0 : ℚ) ≤ 32 * s + 31 := by omega
    have hj' : ¬j < (run p).size := by rw [run_size]; exact hj
    simpa only [Array.getD_eq_getD_getElem?, getElem?_neg (run p) j hj', Option.getD_none] using hWidth

theorem prefix_wordBounds {p : RationalRoundingPair} {s : ℕ} (h : p.FieldsHeight s) (hs : 2 ≤ s) (k : ℕ) :
    RationalArithmeticProgram.WordBounds
      (RationalArithmeticProgram.run (RealPairProgram.code.take k) (inputs p)) (32 * s + 31) := by
  have hZero : rationalWordWidth (0 : ℚ) = 3 := by decide
  exact (final_wordBounds h hs).prefix (by omega) k

def sourceReadCost (p : RationalRoundingPair) : ℕ :=
  rationalWordWidth p.lengthI + rationalWordWidth p.lengthJ +
    rationalWordWidth p.resourceI + rationalWordWidth p.resourceJ

def finalReadCost (p : RationalRoundingPair) : ℕ :=
  rationalWordWidth ((run p).getD 7 0) + rationalWordWidth ((run p).getD 8 0) +
    rationalWordWidth ((run p).getD 11 0)

def preparationBitCost (model : RationalCostModel) (p : RationalRoundingPair) : ℕ :=
  sourceReadCost p + RationalArithmeticProgram.registerCopyCost (inputs p) +
    RationalArithmeticProgram.bitCost model RealPairProgram.code (inputs p) + finalReadCost p

theorem preparationBitCost_bound_of_final (model : RationalCostModel) (p : RationalRoundingPair)
    (W : ℕ) (hZero : rationalWordWidth (0 : ℚ) ≤ W)
    (hFinal : RationalArithmeticProgram.WordBounds (run p) W) :
    preparationBitCost model p ≤ 96 * model.rat W := by
  have hInputs : RationalArithmeticProgram.WordBounds (inputs p) W := hFinal.before_run hZero
  have hCopy := RationalArithmeticProgram.registerCopyCost_bound model (inputs p) W hInputs
  change RationalArithmeticProgram.registerCopyCost (inputs p) ≤ 5 * model.rat W at hCopy
  have hCode := RationalArithmeticProgram.bitCost_bound model RealPairProgram.code (inputs p) W hZero hFinal
  change RationalArithmeticProgram.bitCost model RealPairProgram.code (inputs p) ≤
    RealArithmeticProgram.conservativeWork 5 RealPairProgram.code * model.rat W at hCode
  rw [RealPairProgram.conservativeWork] at hCode
  have hLI : rationalWordWidth p.lengthI ≤ model.rat W := by
    simpa [inputs] using (hInputs 0).trans (model.word_le W)
  have hLJ : rationalWordWidth p.lengthJ ≤ model.rat W := by
    simpa [inputs] using (hInputs 1).trans (model.word_le W)
  have hRI : rationalWordWidth p.resourceI ≤ model.rat W := by
    simpa [inputs] using (hInputs 2).trans (model.word_le W)
  have hRJ : rationalWordWidth p.resourceJ ≤ model.rat W := by
    simpa [inputs] using (hInputs 3).trans (model.word_le W)
  have hSource : sourceReadCost p ≤ 4 * model.rat W := by unfold sourceReadCost; omega
  have hLower := (hFinal 7).trans (model.word_le W)
  have hUpper := (hFinal 8).trans (model.word_le W)
  have hProbability := (hFinal 11).trans (model.word_le W)
  have hFinalReads : finalReadCost p ≤ 3 * model.rat W := by unfold finalReadCost; omega
  unfold preparationBitCost
  omega

theorem preparationBitCost_bound (model : RationalCostModel) {p : RationalRoundingPair} {s : ℕ}
    (h : p.FieldsHeight s) (hs : 2 ≤ s) :
    preparationBitCost model p ≤ 96 * model.rat (32 * s + 31) := by
  have hZero : rationalWordWidth (0 : ℚ) = 3 := by decide
  exact preparationBitCost_bound_of_final model p (32 * s + 31) (by omega) (final_wordBounds h hs)

theorem fieldsHeight_lattice (p : RationalRoundingPair) {D : ℕ} (hD : 0 < D) (h : p.Lattice D)
    (hi : p.lengthI ≤ 1) (hj : p.lengthJ ≤ 1) : p.FieldsHeight (2 + binaryWordWidth D) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (rationalHeight_unit_lattice hD h.lengthI ⟨p.interiorI.1.le.trans p.interiorI.2.le, hi⟩).mono (by omega)
  · exact (rationalHeight_unit_lattice hD h.lengthJ ⟨p.interiorJ.1.le.trans p.interiorJ.2.le, hj⟩).mono (by omega)
  · exact (rationalHeight_unit_lattice hD h.resourceI ⟨le_of_lt p.interiorI.1, p.interiorI.2.le.trans hi⟩).mono (by omega)
  · exact (rationalHeight_unit_lattice hD h.resourceJ ⟨le_of_lt p.interiorJ.1, p.interiorJ.2.le.trans hj⟩).mono (by omega)

theorem preparationBitCost_lattice (model : RationalCostModel) (p : RationalRoundingPair)
    {D : ℕ} (hD : 0 < D) (h : p.Lattice D) (hi : p.lengthI ≤ 1) (hj : p.lengthJ ≤ 1) :
    preparationBitCost model p ≤ 96 * model.rat (32 * binaryWordWidth D + 95) := by
  have hp := preparationBitCost_bound model (fieldsHeight_lattice p hD h hi hj) (by omega)
  have hWidth : 32 * (2 + binaryWordWidth D) + 31 = 32 * binaryWordWidth D + 95 := by omega
  rw [hWidth] at hp
  exact hp

end Blotto.RationalPairProgram
