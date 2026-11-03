import Blotto.GeneralPaperEqualResourceHeadline

/-! Uniform capacity includes the measured sizing computation itself.
Its word-growth bound may depend on the reference and program coefficient
through their encoded lengths. One coefficient is fixed for the full domain;
no per-input profile evaluation or memory census is executed. -/
namespace Blotto.GeneralPaperSelfReferenceCapacity
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

theorem square_le_power : ∀ n : ℕ, 4 ≤ n → n * n ≤ 2 ^ n := by
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
    intro hn
    by_cases h : n < 4
    · have he : n = 3 := by omega
      subst n
      decide
    · have hp := ih (by omega)
      have hSquare : (n + 1) * (n + 1) ≤ 2 * (n * n) := by nlinarith
      simp only [pow_succ]
      nlinarith only [hp, hSquare]

theorem fixed_coefficient (C : ℕ) :
    C * (2 * (4 * C + 8) + 5) ≤ 2 ^ (4 * C + 8) := by
  have h := square_le_power (4 * C + 8) (by omega)
  nlinarith only [h]

/-- P may include all native prices, counters and the sizing computation.
The witness K is global. Actual execution only constructs K * L x. -/
theorem uniform_capacity {α : Type*} (P : ℕ → ℕ → α → ℕ) (L : α → ℕ)
    (hL : ∀ x, 1 ≤ L x)
    (hGrowth : ∃ C : ℕ, ∀ (x : α) (W K : ℕ),
      binaryWordWidth (P W K x) ≤ C * (L x + binaryWordWidth W + binaryWordWidth K)) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ x, P (K * L x) K x < 2 ^ (K * L x) := by
  obtain ⟨C, hC⟩ := hGrowth
  let r := 4 * C + 8
  let K := 2 ^ r
  have hFixed : C * (2 * r + 5) ≤ K := fixed_coefficient C
  have hWordK : binaryWordWidth K = r + 1 := by
    simp only [K, binaryWordWidth, Nat.log2_two_pow]
  refine ⟨K, Nat.one_le_two_pow, fun x => ?_⟩
  have hW := binaryWordWidth_mul K (L x)
  have hWL : binaryWordWidth (L x) ≤ L x + 1 := by
    have h := Nat.log2_le_self (L x)
    unfold binaryWordWidth
    omega
  have hEnvelope : 2 * L x + 2 * r + 3 ≤ (2 * r + 5) * L x := by
    have h := hL x
    nlinarith only [h]
  have hBound : binaryWordWidth (P (K * L x) K x) ≤ K * L x := by
    calc
      _ ≤ C * (L x + binaryWordWidth (K * L x) + binaryWordWidth K) := hC x _ _
      _ ≤ C * (2 * L x + 2 * r + 3) := Nat.mul_le_mul_left C (by omega)
      _ ≤ C * ((2 * r + 5) * L x) := Nat.mul_le_mul_left C hEnvelope
      _ = (C * (2 * r + 5)) * L x := by ring
      _ ≤ K * L x := Nat.mul_le_mul_right (L x) hFixed
  exact (lt_pow_binaryWordWidth _).trans_le (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hBound)

end Blotto.GeneralPaperSelfReferenceCapacity
