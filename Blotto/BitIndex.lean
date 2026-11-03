import Blotto.MidpointGrid
import Blotto.BinaryPayloadCore

/-! A concrete encoding of K Boolean inputs into the 2^K midpoint indices.
The first input is the least significant bit. The implementation consumes
exactly K entries; its bijection is used only for distributional analysis. -/

namespace Blotto

def bitIndex : (K : ℕ) → (Fin K → Bool) → Fin (2 ^ K)
  | 0, _ => ⟨0, by simp⟩
  | K + 1, bits =>
    let tail := bitIndex K (Fin.tail bits)
    ⟨2 * tail.val + if bits 0 then 1 else 0, by
      have ht := tail.isLt
      rw [pow_succ]
      split_ifs <;> omega⟩

theorem bitIndex_injective (K : ℕ) : Function.Injective (bitIndex K) := by
  induction K with
  | zero => intro x y _; funext j; exact Fin.elim0 j
  | succ K ih =>
    intro x y he
    have hv := congrArg Fin.val he
    change 2 * (bitIndex K (Fin.tail x)).val + (if x 0 then 1 else 0) =
      2 * (bitIndex K (Fin.tail y)).val + (if y 0 then 1 else 0) at hv
    have hhead : x 0 = y 0 := by
      cases hx : x 0 <;> cases hy : y 0 <;> simp only [hx, hy, Bool.false_eq_true, ite_false, ite_true] at hv ⊢ <;> omega
    have htail : Fin.tail x = Fin.tail y := by
      apply ih
      apply Fin.ext
      rw [hhead] at hv
      omega
    rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y, hhead, htail]

theorem bitIndex_bijective (K : ℕ) : Function.Bijective (bitIndex K) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨bitIndex_injective K, by simp⟩

noncomputable def bitIndexEquiv (K : ℕ) : (Fin K → Bool) ≃ Fin (2 ^ K) :=
  Equiv.ofBijective (bitIndex K) (bitIndex_bijective K)

-- The old tail recursion remains the reference index. The native midpoint
-- materializes the supplied block once and uses the balanced array decoder.
def balancedBitIndex (K : ℕ) (bits : Fin K → Bool) : Fin (2 ^ K) :=
  ⟨BinaryPayload.balancedValue (Array.ofFn bits) 0 K, BinaryPayload.balancedValue_bounds _ _ _⟩

theorem payload_value_eq_bitIndex (read : ℕ → Bool) (pos K : ℕ) (bits : Fin K → Bool)
    (hRead : ∀ j : Fin K, read (pos + j.val) = bits j) :
    BinaryPayload.value read pos K = (bitIndex K bits).val := by
  induction K generalizing pos with
  | zero => rfl
  | succ K ih =>
    have hHead : read pos = bits 0 := by simpa only [Fin.val_zero, Nat.add_zero] using hRead 0
    have hTail : ∀ j : Fin K, read (pos + 1 + j.val) = Fin.tail bits j := by
      intro j
      simpa only [Fin.tail, Fin.val_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hRead j.succ
    have ht := ih (pos + 1) (Fin.tail bits) hTail
    simp only [BinaryPayload.value, bitIndex, ht, hHead]

theorem balancedBitIndex_eq (K : ℕ) (bits : Fin K → Bool) : balancedBitIndex K bits = bitIndex K bits := by
  apply Fin.ext
  change BinaryPayload.balancedValue (Array.ofFn bits) 0 K = (bitIndex K bits).val
  rw [BinaryPayload.balancedValue_eq]
  apply payload_value_eq_bitIndex
  intro j
  simp [Array.getD, j.isLt]

def dyadicMidpointSampleReference (K : ℕ) (bits : Fin K → Bool) : ℚ :=
  ((bitIndex K bits).val * 2 + 1 : ℚ) / (2 ^ (K + 1) : ℕ)

def dyadicMidpointSample (K : ℕ) (bits : Fin K → Bool) : ℚ :=
  ((balancedBitIndex K bits).val * 2 + 1 : ℚ) / (1 <<< (K + 1) : ℕ)

theorem dyadicMidpointSample_refines (K : ℕ) (bits : Fin K → Bool) :
    dyadicMidpointSample K bits = dyadicMidpointSampleReference K bits := by
  simp only [dyadicMidpointSample, dyadicMidpointSampleReference, balancedBitIndex_eq, Nat.shiftLeft_eq, one_mul]

theorem dyadicMidpointSample_real (K : ℕ) (bits : Fin K → Bool) :
    (dyadicMidpointSample K bits : ℝ) = midpoint (bitIndex K bits) := by
  rw [dyadicMidpointSample_refines]
  simp only [dyadicMidpointSampleReference, Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat,
    midpoint, Nat.cast_pow, Nat.cast_ofNat]
  rw [pow_succ]
  field_simp
  ring

theorem dyadicMidpointSample_bounds (K : ℕ) (bits : Fin K → Bool) :
    (0 : ℝ) < dyadicMidpointSample K bits ∧ (dyadicMidpointSample K bits : ℝ) < 1 := by
  rw [dyadicMidpointSample_real]
  exact midpoint_bounds (pow_pos (by decide) _) _

theorem dyadicMidpointSample_numerator (K : ℕ) (bits : Fin K → Bool) :
    1 ≤ 2 * (bitIndex K bits).val + 1 ∧ 2 * (bitIndex K bits).val + 1 < 2 ^ (K + 1) := by
  have ht := (bitIndex K bits).isLt
  rw [pow_succ]
  omega

def bitIndexReads : ℕ → ℕ
  | 0 => 0
  | K + 1 => bitIndexReads K + 1

theorem bitIndexReads_eq (K : ℕ) : bitIndexReads K = K := by
  induction K with
  | zero => rfl
  | succ K ih => simp only [bitIndexReads, ih]

end Blotto
