import Blotto.PlayerSpecificAlgebraicTerminalLeafBounds

/-! The actual finite-bit allocation draw reserves a fixed resource prefix
and an independent terminal suffix. It runs the reached grouping, local
core and direct original-leaf output, without a Boolean path oracle. -/
namespace Blotto.PlayerSpecificAlgebraicFiniteDraw
set_option autoImplicit false

def bitCount (N H K : ℕ) : ℕ := (N-1)*H+PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K

def resourceBits (N H K : ℕ) (bits : Fin (bitCount N H K) → Bool) : Fin ((N-1)*H) → Bool :=
  firstBitBlock ((N-1)*H) (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) bits

def terminalBits (N H K : ℕ) (bits : Fin (bitCount N H K) → Bool) :
    Fin (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) → Bool :=
  secondBitBlock ((N-1)*H) (PlayerSpecificAlgebraicTerminalCoreDraw.bitCount H K) bits

def draw {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (B : ℚ) (player : Bool) (H K : ℕ)
    (bits : Fin (bitCount N H K) → Bool) : FixedArrayTable N PlayerSpecificDensePolynomial.Data :=
  let s := PlayerSpecificFiniteResourceLoop.draw p player H (resourceBits N H K bits)
  PlayerSpecificAlgebraicTerminalLeafExecution.run p s.1 (if player then 1 else B) H K (terminalBits N H K bits)

theorem random_bit_budget (N H K : ℕ) : bitCount N H K ≤ (N+1000)*H+2*K := by
  have h := Nat.mul_le_mul_right H (show N-1+80 ≤ N+1000 by omega)
  dsimp [bitCount,PlayerSpecificAlgebraicTerminalCoreDraw.bitCount]
  nlinarith only [h]

end Blotto.PlayerSpecificAlgebraicFiniteDraw
