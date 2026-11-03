import Blotto.RationalArithmeticProgram
import Blotto.RealPairProgram
import Blotto.RationalRoundingPair

/-! Both pair-rounding models execute the same seven register instructions.
The rational array is native and shared across endpoint/probability extraction. -/

namespace Blotto.RationalPairProgram

def inputs (p : RationalRoundingPair) : Array ℚ :=
  #[p.lengthI, p.lengthJ, p.resourceI, p.resourceJ, 0]

def run (p : RationalRoundingPair) : Array ℚ := RationalArithmeticProgram.run RealPairProgram.code (inputs p)

theorem run_eq (p : RationalRoundingPair) : run p =
    #[p.lengthI, p.lengthJ, p.resourceI, p.resourceJ, 0, p.total, p.total - p.lengthJ,
      p.lower, p.upper, p.resourceI - p.lower, p.upper - p.lower, p.probability] := by
  simp [run, inputs, RealPairProgram.code, RationalArithmeticProgram.run, RealArithmeticInstruction.executeRat,
    RealArithmeticOp.applyRat, RationalRoundingPair.total, RationalRoundingPair.lower,
    RationalRoundingPair.upper, RationalRoundingPair.probability]

theorem run_lower (p : RationalRoundingPair) : (run p).getD 7 0 = p.lower := by rw [run_eq]; simp
theorem run_upper (p : RationalRoundingPair) : (run p).getD 8 0 = p.upper := by rw [run_eq]; simp
theorem run_probability (p : RationalRoundingPair) : (run p).getD 11 0 = p.probability := by rw [run_eq]; simp
theorem run_size (p : RationalRoundingPair) : (run p).size = 12 := by rw [run_eq]; rfl

theorem denominator_positive (p : RationalRoundingPair) : 0 < (run p).getD 10 0 := by
  have h := sub_pos.mpr p.real.lower_lt_upper
  rw [← p.upper_real, ← p.lower_real] at h
  have hQ : (0 : ℚ) < p.upper - p.lower := by exact_mod_cast h
  rw [run_eq]
  simpa using hQ

def words (p : RationalRoundingPair) (registers : Array ℚ) (h : registers = run p) : ProbabilityWords :=
  ProbabilityWords.ofRat (registers.getD 11 0) (by
    rw [h, run_probability]
    exact ⟨p.probability_bounds.1.le, p.probability_bounds.2.le⟩)

theorem words_eq (p : RationalRoundingPair) (registers : Array ℚ) (h : registers = run p) :
    words p registers h = p.words := by
  subst registers
  unfold words RationalRoundingPair.words
  simp only [run_probability]

end Blotto.RationalPairProgram
