import Blotto.BinaryWordWidthCore

/-! Portable least-significant-bit-first payloads. The value recursion is a
specification; the runtime decoder uses one buffer and balanced block merges. -/

namespace Blotto.BinaryPayload

def value (bits : ℕ → Bool) (pos : ℕ) : ℕ → ℕ
  | 0 => 0
  | length + 1 => 2 * value bits (pos + 1) length + if bits pos then 1 else 0

theorem value_congr (a b : ℕ → Bool) (pa pb length : ℕ)
    (h : ∀ j, a (pa + j) = b (pb + j)) : value a pa length = value b pb length := by
  induction length generalizing pa pb with
  | zero => rfl
  | succ length ih =>
    have hHead : a pa = b pb := by simpa using h 0
    have hTail : ∀ j, a (pa + 1 + j) = b (pb + 1 + j) := by
      intro j
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h (j + 1)
    simp only [value, ih _ _ hTail, hHead]

theorem value_split (bits : ℕ → Bool) (pos low high : ℕ) :
    value bits pos (low + high) = value bits pos low + (value bits (pos + low) high <<< low) := by
  induction low generalizing pos with
  | zero => simp [value]
  | succ low ih =>
    rw [Nat.succ_add]
    simp only [value, ih]
    have hPos : pos + 1 + low = pos + (low + 1) := by omega
    rw [hPos]
    simp only [Nat.shiftLeft_eq, pow_succ]
    ring

theorem value_bounds (bits : ℕ → Bool) (pos length : ℕ) : value bits pos length < 2 ^ length := by
  induction length generalizing pos with
  | zero => simp [value]
  | succ length ih =>
    have h := ih (pos + 1)
    simp only [value, pow_succ]
    split <;> omega

theorem value_testBits (n length : ℕ) (h : n < 2 ^ length) : value n.testBit 0 length = n := by
  induction length generalizing n with
  | zero =>
    have hn : n = 0 := by simpa using h
    simp [value, hn]
  | succ length ih =>
    have hDiv : n / 2 < 2 ^ length := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by simpa [pow_succ] using h)
    have hTail : value n.testBit 1 length = value (n / 2).testBit 0 length :=
      value_congr _ _ 1 0 length (by intro j; simpa [Nat.add_comm] using Nat.testBit_succ n j)
    have hMod := Nat.mod_add_div n 2
    simp only [value, Nat.zero_add, hTail, ih _ hDiv, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one n with hZero | hOne
    · simp only [hZero, Nat.zero_ne_one, decide_false, Bool.false_eq_true, ite_false]
      omega
    · simp only [hOne, decide_true, ite_true]
      omega

def bits (length n : ℕ) : List Bool := List.ofFn (fun j : Fin length => n.testBit j.val)

theorem bits_length (length n : ℕ) : (bits length n).length = length := by simp [bits]

def balancedValue (buffer : Array Bool) (pos length : ℕ) : ℕ :=
  if length = 0 then 0 else if length = 1 then if buffer.getD pos false then 1 else 0 else
    let low := length / 2
    balancedValue buffer pos low + (balancedValue buffer (pos + low) (length - low) <<< low)
termination_by length
decreasing_by all_goals omega

theorem balancedValue_eq (buffer : Array Bool) (pos length : ℕ) :
    balancedValue buffer pos length = value (fun j => buffer.getD j false) pos length := by
  unfold balancedValue
  split
  · rename_i hz; simp [hz, value]
  · split
    · rename_i hOne; simp [hOne, value]
    · dsimp only
      have hLow := balancedValue_eq buffer pos (length / 2)
      have hHigh := balancedValue_eq buffer (pos + length / 2) (length - length / 2)
      rw [hLow, hHigh]
      have hSum : length / 2 + (length - length / 2) = length := by omega
      rw [← value_split, hSum]
termination_by length
decreasing_by all_goals omega

theorem balancedValue_bounds (buffer : Array Bool) (pos length : ℕ) : balancedValue buffer pos length < 2 ^ length := by
  rw [balancedValue_eq]
  exact value_bounds _ pos length

def decode (payload : List Bool) : ℕ := balancedValue payload.toArray 0 payload.length

theorem decode_bits (length n : ℕ) (h : n < 2 ^ length) : decode (bits length n) = n := by
  rw [decode, balancedValue_eq, bits_length]
  have hEq : value (fun j => (bits length n).toArray.getD j false) 0 length = value n.testBit 0 length := by
    apply value_congr
    intro j
    simp only [Nat.zero_add]
    by_cases hj : j < length
    · simp [bits, Array.getD, hj]
    · have hPower : 2 ^ length ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
      have hBit := Nat.testBit_lt_two_pow (h.trans_le hPower)
      simp [bits, Array.getD, hj, hBit]
  rw [hEq]
  exact value_testBits n length h

end Blotto.BinaryPayload
