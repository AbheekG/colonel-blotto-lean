import Blotto.GeneralPaperEqualBitMidpoint

/-! An indexed constructor obtains its runtime length from a stored array
descriptor. The equality index transports types only; it does not reconstruct
an input group/route/formula description during a draw. -/
namespace Blotto.GeneralPaperSizedBitArray
set_option autoImplicit false

def run {α : Type*} {r : ℕ} (size : ℕ) (hSize : size = r) (A : ℕ)
    (body : Fin r → α × ℕ) : FixedArrayTable r α × ℕ :=
  let actual := PaperIndexedArrayConstruction.run (fun w => w) A (fun i : Fin size => body (i.cast hSize))
  (⟨actual.1.data, actual.1.size.trans hSize⟩, actual.2)

theorem eq_run {α : Type*} {r : ℕ} (size : ℕ) (hSize : size = r) (A : ℕ)
    (body : Fin r → α × ℕ) : run size hSize A body = PaperIndexedArrayConstruction.run (fun w => w) A body := by
  cases hSize
  rfl

end Blotto.GeneralPaperSizedBitArray
