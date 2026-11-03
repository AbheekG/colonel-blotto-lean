import Blotto.GeneralPaperParametricRecursionPrice

/-! Uniform batch envelopes for every native parametric stage. Only the
number of visited fields multiplies the stage price in the complete loop.
-/
namespace Blotto.GeneralPaperParametricPriceProfiles
set_option autoImplicit false

theorem stage_batch_mono {n q : ℕ} (h : n≤q) (m S K W P : ℕ) :
    GeneralPaperParametricStageBits.profile n m S K W P≤GeneralPaperParametricStageBits.profile q m S K W P := by
  have hw := binaryWordWidth_mono (Nat.add_le_add_right h 3)
  unfold GeneralPaperParametricStageBits.profile
  gcongr

theorem stage_price_mono (n m S K W : ℕ) {P Q : ℕ} (h : P≤Q) :
    GeneralPaperParametricStageBits.profile n m S K W P≤GeneralPaperParametricStageBits.profile n m S K W Q := by
  unfold GeneralPaperParametricStageBits.profile GeneralPaperAffineStepPrice.profile
  gcongr

def profile (r m S K W P : ℕ) : ℕ :=
  GeneralPaperParametricRecursionPrice.profile r W (120*(S+1)*W)
    (GeneralPaperParametricStageBits.profile ((S+1)*(K*K)) m S K W P)

end Blotto.GeneralPaperParametricPriceProfiles
