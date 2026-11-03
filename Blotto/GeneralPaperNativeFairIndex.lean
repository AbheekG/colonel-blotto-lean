import Blotto.GeneralPaperNativeCompiledEquilibrium
import Blotto.FairBitProductLaw

/-! Read one stored little-endian bit block by forward indexed loads.
Value/power/read-count accumulators use only addition and doubling; no
quotient, remainder, input-encoding query or random-access bit oracle is
used. All actual arithmetic operands, indices and writes are priced. -/
namespace Blotto.GeneralPaperNativeFairIndex
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure State where
  value : ℕ
  power : ℕ
  reads : ℕ
  work : ℕ

def loop {N : ℕ} (primitive : ℕ → ℕ) (A : ℕ) (buffer : FixedArrayTable N Bool)
    (offset total : ℕ) (hBuffer : offset+total≤N) : (count : ℕ) → count≤total → State
  | 0,_ => ⟨0,1,0,32*A⟩
  | count+1,hCount =>
    let previous := loop primitive A buffer offset total hBuffer count (by omega)
    let position := offset+count
    let bit := buffer.read ⟨position,by omega⟩
    let added := if bit then previous.power else 0
    ⟨previous.value+added,2*previous.power,previous.reads+1,
      previous.work+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) offset count+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) previous.value added+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 2 previous.power+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) previous.reads 1+
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) count 1+64*A⟩

theorem power {N : ℕ} (primitive : ℕ → ℕ) (A : ℕ) (buffer : FixedArrayTable N Bool)
    (offset total : ℕ) (hBuffer : offset+total≤N) (count : ℕ) (hCount : count≤total) :
    (loop primitive A buffer offset total hBuffer count hCount).power=2^count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [loop,ih (by omega),pow_succ]
    omega

theorem reads {N : ℕ} (primitive : ℕ → ℕ) (A : ℕ) (buffer : FixedArrayTable N Bool)
    (offset total : ℕ) (hBuffer : offset+total≤N) (count : ℕ) (hCount : count≤total) :
    (loop primitive A buffer offset total hBuffer count hCount).reads=count := by
  induction count with
  | zero => rfl
  | succ count ih => exact congrArg (fun x => x+1) (ih (by omega))

theorem bounded {N : ℕ} (primitive : ℕ → ℕ) (A : ℕ) (buffer : FixedArrayTable N Bool)
    (offset total : ℕ) (hBuffer : offset+total≤N) (count : ℕ) (hCount : count≤total) :
    (loop primitive A buffer offset total hBuffer count hCount).value<2^count := by
  induction count with
  | zero => norm_num [loop]
  | succ count ih =>
    have hh := ih (by omega)
    simp only [loop,power,pow_succ]
    split <;> omega

theorem data {N : ℕ} (primitive : ℕ → ℕ) (A : ℕ) (buffer : FixedArrayTable N Bool)
    (offset total : ℕ) (hBuffer : offset+total≤N) (count : ℕ) (hCount : count≤total) :
    (loop primitive A buffer offset total hBuffer count hCount).value=
      BinaryPayload.value (fun i => buffer.data.getD i false) offset count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have he := BinaryPayload.value_split (fun i => buffer.data.getD i false) offset count 1
    have hRead : buffer.data.getD (offset+count) false=buffer.read ⟨offset+count,by omega⟩ := by
      simp only [FixedArrayTable.read,Array.getD]
      rw [dite_eq_left (by rw [buffer.size];omega)]
      rfl
    simp only [loop,ih (by omega),power]
    rw [he]
    simp only [BinaryPayload.value,Nat.zero_add,Nat.mul_zero,Nat.shiftLeft_eq,hRead]
    split <;> simp only [Nat.one_mul,Nat.zero_mul]

theorem arithmetic_work {N : ℕ} (A : ℕ) (buffer : FixedArrayTable N Bool)
    (offset total : ℕ) (hBuffer : offset+total≤N) (count : ℕ) (hCount : count≤total) :
    (loop (fun _ => 1) A buffer offset total hBuffer count hCount).work≤count*(10+64*A)+32*A := by
  induction count with
  | zero => simp only [loop,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ count ih =>
    have hh := ih (by omega)
    simp only [loop,GeneralPaperNaturalPrimitivePrice.binary]
    nlinarith only [hh]

end Blotto.GeneralPaperNativeFairIndex
