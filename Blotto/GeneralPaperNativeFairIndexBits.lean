import Blotto.GeneralPaperNativeFairEveryOutput

/-! Operand-sensitive bit price of the actual forward dyadic decoder.
The magnitude/width functions below are erased proof bounds and never
decoder inputs. Native arithmetic constructs its growing power directly. -/
namespace Blotto.GeneralPaperNativeFairIndexBits
open GeneralPaperNativeFairIndex
set_option autoImplicit false
set_option maxHeartbeats 3500000

def magnitude (N total : ℕ) : ℕ := N+2^total+2
def width (N total : ℕ) : ℕ := 1+binaryWordWidth (magnitude N total)

theorem work {N : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (A : ℕ) (buffer : FixedArrayTable N Bool)
    (offset total : ℕ) (hBuffer : offset+total≤N) (count : ℕ) (hCount : count≤total) :
    (loop primitive A buffer offset total hBuffer count hCount).work≤
      count*(10*primitive (width N total)+64*A)+32*A := by
  let M := magnitude N total
  let P := primitive (width N total)
  have hPowPositive := Nat.two_pow_pos total
  have hN : N≤M := by dsimp only [M,magnitude];omega
  have hPow : 2^total≤M := by dsimp only [M,magnitude];omega
  have hTwo : 2≤M := by dsimp only [M,magnitude];omega
  induction count with
  | zero => simp only [loop,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ count ih =>
    let previous := loop primitive A buffer offset total hBuffer count (by omega)
    let added := if buffer.read ⟨offset+count,by omega⟩ then previous.power else 0
    have hi := ih (by omega)
    have hCountN : count+1≤N := by omega
    have hP : previous.power=2^count := power primitive A buffer offset total hBuffer count (by omega)
    have hV : previous.value<2^count := bounded primitive A buffer offset total hBuffer count (by omega)
    have hReads : previous.reads=count := reads primitive A buffer offset total hBuffer count (by omega)
    have hpc : 2^count≤2^total := Nat.pow_le_pow_right (by decide) (by omega)
    have hpn : 2^(count+1)≤2^total := Nat.pow_le_pow_right (by decide) hCount
    have ha : added≤previous.power := by dsimp only [added];split <;> omega
    have hAdd : previous.value+added≤M := by
      have hh : previous.value+added<2^(count+1) := by rw [pow_succ];omega
      exact hh.le.trans (hpn.trans hPow)
    have hDouble : 2*previous.power≤M := by
      rw [hP]
      simpa only [pow_succ,Nat.mul_comm] using hpn.trans hPow
    have hb := GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono
    have h1 := hb (fun a b => a+b) offset count M (by omega) (by omega) (by omega)
    have h2 := hb (fun a b => a+b) previous.value added M
      ((hV.le.trans hpc).trans hPow) (ha.trans (by rw [hP];exact hpc.trans hPow)) hAdd
    have h3 := hb (fun a b => a*b) 2 previous.power M hTwo (by rw [hP];exact hpc.trans hPow) hDouble
    have h4 := hb (fun a b => a+b) previous.reads 1 M (by omega) (by omega) (by omega)
    have h5 := hb (fun a b => a+b) count 1 M (by omega) (by omega) (by omega)
    change previous.work≤count*(10*P+64*A)+32*A at hi
    change _≤2*P at h1 h2 h3 h4 h5
    change previous.work+_+_+_+_+_+64*A≤(count+1)*(10*P+64*A)+32*A
    nlinarith only [hi,h1,h2,h3,h4,h5]

end Blotto.GeneralPaperNativeFairIndexBits
