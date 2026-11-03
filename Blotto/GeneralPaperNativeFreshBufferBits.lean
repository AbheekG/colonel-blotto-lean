import Blotto.GeneralPaperNativeFairIndexBits

/-! Complete operand/control bit price for the actual fresh-bit buffer.
The size bound is erased; it does not supply a runtime capacity oracle. -/
namespace Blotto.GeneralPaperNativeFreshBufferBits
open GeneralPaperNativeFreshBuffer
set_option autoImplicit false
set_option maxHeartbeats 3500000

def width (B : ℕ) : ℕ := 1+binaryWordWidth (B+2)

theorem fill_work {B : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (A : ℕ)
    (fresh : Fin B → Bool) (k : ℕ) (hk : k≤B) :
    (fill primitive A fresh k hk).work≤k*(5*primitive (width B)+64*A+1)+32*A := by
  let P := primitive (width B)
  induction k with
  | zero => simp only [fill,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ k ih =>
    have hi := ih (by omega)
    let previous := fill primitive A fresh k (by omega)
    have hr : previous.reads=k := reads primitive A fresh k (by omega)
    have hb := GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono
    have h1 := hb (fun a b => a+b) previous.reads 1 (B+2) (by omega) (by omega) (by omega)
    have h2 := hb (fun a b => a+b) k 1 (B+2) (by omega) (by omega) (by omega)
    have hc := hMono (Nat.add_le_add_left (binaryWordWidth_mono (by omega : k+1≤B+2)) 1)
    change _≤2*P at h1 h2
    change _≤P at hc
    change previous.work≤k*(5*P+64*A+1)+32*A at hi
    change previous.work+_+_+_+64*A+1≤(k+1)*(5*P+64*A+1)+32*A
    nlinarith only [hi,h1,h2,hc]

def profile (primitive : ℕ → ℕ) (A B : ℕ) : ℕ := B*(5*primitive (width B)+64*A+1)+64*A

theorem work {B : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (A : ℕ) (fresh : Fin B → Bool) :
    (run primitive A fresh).2≤profile primitive A B := by
  have hh := fill_work primitive hMono A fresh B le_rfl
  change (fill primitive A fresh B le_rfl).work+32*A≤_
  unfold profile
  omega

end Blotto.GeneralPaperNativeFreshBufferBits
