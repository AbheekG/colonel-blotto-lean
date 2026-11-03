import Blotto.GeneralPaperLocalEpochExecution

/-! The retained trajectory capacity bounds every loop/index word.
No bit length is queried by the arithmetic interpretation. -/
namespace Blotto.GeneralPaperLocalEpochControlPrice
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem scalar_word (cap x : ℕ) (hx : x≤cap+1) : 1+binaryWordWidth x≤1+binaryWordWidth (cap+1) :=
  Nat.add_le_add_left (binaryWordWidth_mono hx) 1

theorem guard (index : ℕ → ℕ) (hMono : Monotone index) (A cap x : ℕ) (hx : x≤cap+1)
    (hIndex : index (1+binaryWordWidth (cap+1))≤A) : GeneralPaperIntegerWordPrice.compare index x 0≤A :=
  (GeneralPaperIntegerWordPrice.compare_le index hMono x 0 _ (scalar_word cap x hx) (scalar_word cap 0 (Nat.zero_le _))).trans hIndex

theorem control (index : ℕ → ℕ) (hMono : Monotone index) (A cap x : ℕ) (hx : x≤cap+1)
    (hIndex : index (1+binaryWordWidth (cap+1))≤A) : GeneralPaperLocalEpochExecution.control index A x≤131*A := by
  have hg := guard index hMono A cap x hx hIndex
  have hs := (GeneralPaperNaturalPrimitivePrice.binary_le index hMono (fun a b => a-b) x 1 (cap+1)
    hx (by omega) ((Nat.sub_le _ _).trans hx)).trans (Nat.mul_le_mul_left 2 hIndex)
  unfold GeneralPaperLocalEpochExecution.control
  omega

theorem initial (index : ℕ → ℕ) (hMono : Monotone index) (A cap : ℕ) (hA : 1≤A)
    (hIndex : index (1+binaryWordWidth (cap+1))≤A) :
    PaperIndexedArrayConstruction.initialWork index A cap+GeneralPaperIntegerWordPrice.compare index 0 0+64*A≤256*A := by
  have hi := (hMono (show binaryWordWidth (cap+1)≤1+binaryWordWidth (cap+1) by omega)).trans hIndex
  have hg := guard index hMono A cap 0 (Nat.zero_le _) hIndex
  unfold PaperIndexedArrayConstruction.initialWork
  omega

theorem step (index : ℕ → ℕ) (hMono : Monotone index) (A cap count : ℕ) (hA : 1≤A) (hc : count≤cap)
    (hIndex : index (1+binaryWordWidth (cap+1))≤A) :
    PaperIndexedArrayConstruction.stepWork index A count+GeneralPaperLocalEpochExecution.control index A (count+1)≤256*A := by
  have hi := (hMono ((binaryWordWidth_mono (Nat.add_le_add_right hc 1)).trans (by omega))).trans hIndex
  have hg := control index hMono A cap (count+1) (by omega) hIndex
  unfold PaperIndexedArrayConstruction.stepWork
  omega

end Blotto.GeneralPaperLocalEpochControlPrice
