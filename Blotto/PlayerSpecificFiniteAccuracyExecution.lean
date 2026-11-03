import Blotto.PlayerSpecificRationalPrecisionExecution

/-! The three numerical precisions are actually computed once from the
requested error and the positive minimum exponent. The coin scale and
final output addition are measured natural operations. -/
namespace Blotto.PlayerSpecificFiniteAccuracyExecution
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frame (N s : ℕ) (epsilon : ℚ) (scale scalar coin output rounded : ℕ) : Trace :=
  copyRow [epsilon]++[.control N,.control s,.control scale,.control scalar,
    .control coin,.control output,.control rounded]

def run (N s : ℕ) (epsilon : ℚ) : PlayerSpecificFiniteAccuracy.Parameters×ℕ :=
  let model:=RationalCostModel.schoolbook
  let nplus:=PlayerSpecificNaturalExecution.binary model (fun a b=>a+b) N 1000
  let scale:=PlayerSpecificNaturalExecution.binary model (fun a b=>a*b) 32 nplus.1
  let scalar:=PlayerSpecificRationalPrecisionExecution.run 48 epsilon
  let coin:=PlayerSpecificRationalPrecisionExecution.run scale.1 epsilon
  let output:=PlayerSpecificRationalPrecisionExecution.run 32 epsilon
  let rounded:=PlayerSpecificNaturalExecution.binary model (fun a b=>a+b) s output.1
  (⟨scalar.1,coin.1,rounded.1⟩,
    nplus.2+scale.2+scalar.2+coin.2+output.2+rounded.2+
      price model (frame N s epsilon scale.1 scalar.1 coin.1 output.1 rounded.1))

theorem value (N s : ℕ) (epsilon : ℚ) (he : 0<epsilon) :
    (run N s epsilon).1=PlayerSpecificFiniteAccuracy.prepare N s epsilon := by
  have hs : 0<32*(N+1000) := by omega
  simp only [run,PlayerSpecificNaturalExecution.binary_value,
    PlayerSpecificRationalPrecisionExecution.value 48 epsilon (by decide) he,
    PlayerSpecificRationalPrecisionExecution.value (32*(N+1000)) epsilon hs he,
    PlayerSpecificRationalPrecisionExecution.value 32 epsilon (by decide) he,
    PlayerSpecificFiniteAccuracy.prepare]

theorem random_bits (N s : ℕ) (epsilon : ℚ) (he : 0<epsilon) :
    let a:=(run N s epsilon).1
    PlayerSpecificAlgebraicFiniteDraw.bitCount N a.coinBits a.scalarBits≤
      (N+1000)*(⌈Real.logb 2 (1/(epsilon:ℝ))⌉₊+binaryWordWidth (N+1000)+6)+
        2*(⌈Real.logb 2 (1/(epsilon:ℝ))⌉₊+6) := by
  rw [value N s epsilon he]
  exact PlayerSpecificFiniteAccuracy.random_bit_budget N s epsilon he

end Blotto.PlayerSpecificFiniteAccuracyExecution
