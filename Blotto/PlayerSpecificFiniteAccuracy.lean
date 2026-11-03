import Blotto.PlayerSpecificRationalPrecisionLog

/-! Actual numerical preparation of the scalar, Bernoulli and output
precisions specified in the player-specific finite-bit construction. -/
namespace Blotto.PlayerSpecificFiniteAccuracy
open PlayerSpecificRationalPrecision PlayerSpecificRationalPrecisionLog
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Parameters where
  scalarBits : ℕ
  coinBits : ℕ
  outputBits : ℕ

def prepare (N s : ℕ) (epsilon : ℚ) : Parameters :=
  ⟨exponent 48 epsilon,exponent (32*(N+1000)) epsilon,s+exponent 32 epsilon⟩

theorem exact_precisions (N s : ℕ) (epsilon : ℚ) (he : 0 < epsilon) :
    (prepare N s epsilon).scalarBits=⌈Real.logb 2 (48/(epsilon:ℝ))⌉₊ ∧
      (prepare N s epsilon).coinBits=⌈Real.logb 2 ((32*(N+1000):ℝ)/(epsilon:ℝ))⌉₊ ∧
      (prepare N s epsilon).outputBits=s+⌈Real.logb 2 (32/(epsilon:ℝ))⌉₊ := by
  refine ⟨ceil_eq 48 epsilon he (by decide),?_,congrArg (fun a => s+a) (ceil_eq 32 epsilon he (by decide))⟩
  simpa only [prepare,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using ceil_eq (32*(N+1000)) epsilon he (by omega)

theorem logarithmic_bounds (N s : ℕ) (epsilon : ℚ) (he : 0 < epsilon) :
    let k := ⌈Real.logb 2 (1/(epsilon:ℝ))⌉₊
    (prepare N s epsilon).scalarBits ≤ k+6 ∧
      (prepare N s epsilon).coinBits ≤ k+binaryWordWidth (N+1000)+6 ∧
      (prepare N s epsilon).outputBits ≤ s+k+6 := by
  have h48 := logarithmic_bound 48 epsilon he
  have h32 := logarithmic_bound 32 epsilon he
  have hC := logarithmic_bound (32*(N+1000)) epsilon he
  have hw := binaryWordWidth_mul 32 (N+1000)
  rw [show binaryWordWidth 48=6 by decide] at h48
  rw [show binaryWordWidth 32=6 by decide] at h32 hw
  refine ⟨h48,?_,?_⟩
  · change exponent (32*(N+1000)) epsilon ≤ _
    omega
  · change s+exponent 32 epsilon ≤ _
    omega

theorem random_bit_budget (N s : ℕ) (epsilon : ℚ) (he : 0 < epsilon) :
    let a := prepare N s epsilon
    let k := ⌈Real.logb 2 (1/(epsilon:ℝ))⌉₊
    PlayerSpecificAlgebraicFiniteDraw.bitCount N a.coinBits a.scalarBits ≤
      (N+1000)*(k+binaryWordWidth (N+1000)+6)+2*(k+6) := by
  have h := logarithmic_bounds N s epsilon he
  exact (PlayerSpecificAlgebraicFiniteDraw.random_bit_budget N _ _).trans
    (Nat.add_le_add (Nat.mul_le_mul_left (N+1000) h.2.1) (Nat.mul_le_mul_left 2 h.1))

end Blotto.PlayerSpecificFiniteAccuracy
