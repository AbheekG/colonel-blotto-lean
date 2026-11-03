import Blotto.GeneralPaperNativeFreshBufferBits

/-! Complete local bit price for both disjoint native index blocks and
their read-count addition. Only erased proof widths use dyadic bounds. -/
namespace Blotto.GeneralPaperNativeDyadicBlocksBits
open GeneralPaperNativeDyadicBlocks
set_option autoImplicit false
set_option maxHeartbeats 3500000

def profile (primitive : ℕ → ℕ) (A R L : ℕ) : ℕ :=
  R*(10*primitive (GeneralPaperNativeFairIndexBits.width (R+L) R)+64*A)+
    L*(10*primitive (GeneralPaperNativeFairIndexBits.width (R+L) L)+64*A)+128*A+
    2*primitive (1+binaryWordWidth (R+L+2))

theorem work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (buffer : FixedArrayTable (R+L) Bool) : (run primitive A R L T S hT hS buffer).work≤profile primitive A R L := by
  let row := GeneralPaperNativeFairIndex.loop primitive A buffer 0 R (by omega) R le_rfl
  let shift := GeneralPaperNativeFairIndex.loop primitive A buffer R L le_rfl L le_rfl
  have hr := GeneralPaperNativeFairIndexBits.work primitive hMono A buffer 0 R (by omega) R le_rfl
  have hs := GeneralPaperNativeFairIndexBits.work primitive hMono A buffer R L le_rfl L le_rfl
  have hrr : row.reads=R := GeneralPaperNativeFairIndex.reads primitive A buffer 0 R (by omega) R le_rfl
  have hsr : shift.reads=L := GeneralPaperNativeFairIndex.reads primitive A buffer R L le_rfl L le_rfl
  have hc := GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono (fun a b => a+b) row.reads shift.reads (R+L+2)
    (by omega) (by omega) (by omega)
  change row.work≤_ at hr
  change shift.work≤_ at hs
  change row.work+shift.work+GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) row.reads shift.reads+64*A≤_
  unfold profile
  omega

end Blotto.GeneralPaperNativeDyadicBlocksBits
