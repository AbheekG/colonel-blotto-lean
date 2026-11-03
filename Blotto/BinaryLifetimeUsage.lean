import Blotto.BinaryLifetimeArray
import Blotto.BinaryPRGHeapTraceUsage
import Blotto.BinaryQuadraticSyntaxLifetime

/-! Common retained-cell/activation usage bounds for actual caller arrays,
quadratic opcodes and compiled selected expressions. -/
namespace Blotto.BinaryLifetimeUsage
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryRationalNormalization BinaryRationalEncoding

theorem array_usage {α : Type*} (n : ℕ) (produce : Fin n → α × Trace) (B F : ℕ)
    (hB : ∀ j,listCells (produce j).2 + arraySlots (produce j).2 ≤ B)
    (hF : ∀ j,framePeak (produce j).2 ≤ F) :
    usage (BinaryLifetimeArray.build n produce).2 ≤ n * B + F + 2 * (n + 1)^2 + n + 14 := by
  have h := BinaryLifetimeArray.build_bounds n produce B F hB hF
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells
  nlinarith

def opcodeEnvelope (W : ℕ) : ℕ :=
  BinaryQuadraticLifetime.opcodeBound W + BinaryQuadraticLifetime.opcodeFrames W

theorem opcode_usage (op : RealArithmeticOp) (first second : SignedWord) (W : ℕ)
    (hFirst : width first ≤ W) (hSecond : width second ≤ W) :
    usage (BinaryQuadraticLifetime.applyWithTrace op first second).2 ≤ opcodeEnvelope W := by
  have h := BinaryQuadraticLifetime.applyWithTrace_bounds op first second W hFirst hSecond
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells opcodeEnvelope
  omega

end Blotto.BinaryLifetimeUsage
