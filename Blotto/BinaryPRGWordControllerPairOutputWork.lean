import Blotto.BinaryPRGWordControllerPairOutputs

/-! Own prices for the Boolean register backend from a supplied semantic
trace-width proof. The proof measures this backend's tree preparation, carry
cursor, arithmetic operations, and field reads; it invokes no old work ledger. -/
namespace Blotto.BinaryPRGWordControllerPairOutputWork
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerPairRegisters BinaryPRGWordControllerPairOutputs
open BinaryPRGWordControllerWordStore

def traceBound (W : ℕ) : ℕ :=
  218 + 16 * (1 + 2 * W) + 7 * (instructionBound W + 2) + 1 + 3 * (47 + 2 * W) + 6

theorem prepare_trace_bound (source : BinaryRationalPairProgram.Source) (W : ℕ)
    (hTrace : BinaryRationalRegisterProgram.TraceWordBounds RealPairProgram.code source.inputs W) :
    (prepareWithWork source).2 ≤ traceBound W := by
  have hInitial := initialWithWork_bound source W (trace_start _ _ W hTrace)
  have hTrace' := hTrace
  rw [← code_reference] at hTrace'
  have hProgram := runWithWork_bound code (initial source) source.inputs (initial_refines source)
    source.inputs_valid (by simp [BinaryRationalPairProgram.Source.inputs,code]) W hTrace'
  have hWidths := BinaryRationalRegisterProgram.trace_bounds_final _ _ W hTrace
  change BinaryRationalRegisterProgram.WordBounds source.run W at hWidths
  have h0 := BinaryRationalExpression.payloadWords_bound _ W (hWidths 7)
  have h1 := BinaryRationalExpression.payloadWords_bound _ W (hWidths 8)
  have h2 := BinaryRationalExpression.payloadWords_bound _ W (hWidths 11)
  have hLength : code.length = 7 := rfl
  rw [hLength] at hProgram
  unfold prepareWithWork traceBound
  dsimp only
  rw [lookupCells_exact,lookupCells_exact,lookupCells_exact]
  rw [preparedPairWithWork_erasure,pair_lower,pair_upper,pair_probability]
  change (initialWithWork source).2 + (runWithWork code (initial source)).2 +
    (46 + BinaryRationalExpression.payloadWords (BinaryRationalRegisterProgram.read source.run 7)) +
    (46 + BinaryRationalExpression.payloadWords (BinaryRationalRegisterProgram.read source.run 8)) +
    (46 + BinaryRationalExpression.payloadWords (BinaryRationalRegisterProgram.read source.run 11)) + 6 ≤ _
  omega

/-- A deliberately loose cubic envelope, derived from this backend's own
quadratic price. This comparison never equates different backend work. -/
theorem traceBound_le_cubic (W : ℕ) (hW : 1 ≤ W) :
    traceBound W ≤ 7 * (12000 * (W + 1)^3 + 28 * (1 + 2 * W) + 4) := by
  have hCube : 2 * (W + 1)^2 ≤ (W + 1)^2 * (W + 1) :=
    calc
      2 * (W + 1)^2 ≤ (W + 1) * (W + 1)^2 :=
        Nat.mul_le_mul_right ((W + 1)^2) (show 2 ≤ W + 1 by omega)
      _ = (W + 1)^2 * (W + 1) := Nat.mul_comm _ _
  unfold traceBound BinaryPRGWordControllerPairRegisters.instructionBound
  nlinarith [Nat.zero_le (W^2)]

end Blotto.BinaryPRGWordControllerPairOutputWork
