import Blotto.GeneralPaperAdditivePayloadFillStorage
import Blotto.GeneralPaperEqualInputRates

/-! Literal lifetimes of the actual dominant-field indexed constructor.
The sole original-budget entry is summed once in the buffers and recursive
frames. Per-entry copy scratch is active for one callback at a time. -/
namespace Blotto.GeneralPaperEqualBitVertexLifetime
open GeneralPaperEncodedScalarStorage GeneralPaperNativePayloadFillStorage
open PaperIndexedArrayConstruction
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

def callback {n : ℕ} (W : ℕ) (budget : ℚ) (chosen : Fin n) (j : Fin n) : ℚ × ℕ :=
  let q := if j = chosen then budget else 0
  (q, rationalWordWidth q + 32 * W + 32)

theorem payload_cap {n : ℕ} (W : ℕ) (budget : ℚ) (chosen j : Fin n) :
    rationalWordWidth (callback W budget chosen j).1 ≤ rationalWordWidth budget + 3 := by
  have hZero : rationalWordWidth (0 : ℚ) = 3 := by decide
  unfold callback
  split_ifs <;> dsimp only <;> omega

def copyWindow {n : ℕ} (W : ℕ) (budget : ℚ) (chosen j : Fin n) : ℕ :=
  let c := callback W budget chosen j
  rationalWordWidth c.1 + fields W [c.2, 32 * W, 32] + 64 * W

def callbackPrice (W b : ℕ) : ℕ := b + 32 * W + 35
def copyProfile (W b : ℕ) : ℕ :=
  b + 3 + 3 * (natBits (callbackPrice W b) + W) + 96 * W

theorem work_cap {n : ℕ} (W : ℕ) (budget : ℚ) (chosen j : Fin n) :
    (callback W budget chosen j).2 ≤ callbackPrice W (rationalWordWidth budget) := by
  have hp := payload_cap W budget chosen j
  dsimp only [callback, callbackPrice] at *
  omega

theorem copy_bound {n : ℕ} (W : ℕ) (budget : ℚ) (chosen j : Fin n) :
    copyWindow W budget chosen j ≤ copyProfile W (rationalWordWidth budget) := by
  have hp := payload_cap W budget chosen j
  have hc := work_cap W budget chosen j
  have hf := fields_bound W (natBits (callbackPrice W (rationalWordWidth budget)))
    [(callback W budget chosen j).2, 32 * W, 32] (by
      intro x hx; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> dsimp only [callbackPrice] at * <;> omega)
  change fields W _ ≤ 3 * (natBits (callbackPrice W (rationalWordWidth budget)) + W) + 32 * W at hf
  dsimp only [copyWindow, copyProfile]
  omega

def parentCap (W n b : ℕ) : ℕ := metadataCap W n (callbackPrice W b) + 64 * W + 64

def window {n : ℕ} (W : ℕ) (budget : ℚ) (chosen : Fin n) (k : ℕ) (hk : k ≤ n) : ℕ :=
  GeneralPaperNativePayloadFillStorage.window W rationalWordWidth (callback W budget chosen)
    (copyWindow W budget chosen) k hk +
  fields W [n,chosen.val,(run id W (callback W budget chosen)).2,
    (GeneralPaperEqualBitVertex.run W budget chosen).2,64 * W + 64] + 128 * W

def profile (W n b : ℕ) : ℕ :=
  GeneralPaperAdditivePayloadFillStorage.profile W (3 * n + b) (b + 3) n
    (callbackPrice W b) (copyProfile W b) + 5 * (natBits (parentCap W n b) + W) + 160 * W

theorem all_cursors {n : ℕ} (W : ℕ) (budget : ℚ) (chosen : Fin n)
    (hW : 1 ≤ W) (hIndex : binaryWordWidth (n + 1) ≤ W) (k : ℕ) (hk : k ≤ n) :
    window W budget chosen k hk ≤ profile W n (rationalWordWidth budget) := by
  have hFill := GeneralPaperAdditivePayloadFillStorage.bounded W (3 * n + rationalWordWidth budget)
    (rationalWordWidth budget + 3) (callbackPrice W (rationalWordWidth budget))
    (copyProfile W (rationalWordWidth budget)) rationalWordWidth (callback W budget chosen)
    (copyWindow W budget chosen) (GeneralPaperEqualBitVertex.payload budget chosen)
    (payload_cap W budget chosen) (work_cap W budget chosen) (copy_bound W budget chosen)
    hW hIndex k hk
  have hWork := prefix_work W (callbackPrice W (rationalWordWidth budget))
    (callback W budget chosen) (work_cap W budget chosen) hW hIndex n le_rfl
  change (run id W (callback W budget chosen)).2 ≤ workCap W n (callbackPrice W (rationalWordWidth budget)) at hWork
  have hReturn : (GeneralPaperEqualBitVertex.run W budget chosen).2 =
      (run id W (callback W budget chosen)).2 + 64 * W + 64 := rfl
  have hf := fields_bound W (natBits (parentCap W n (rationalWordWidth budget)))
    [n,chosen.val,(run id W (callback W budget chosen)).2,
      (GeneralPaperEqualBitVertex.run W budget chosen).2,64 * W + 64] (by
        intro x hx; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        all_goals unfold parentCap metadataCap; omega)
  change fields W _ ≤ 5 * (natBits (parentCap W n (rationalWordWidth budget)) + W) + 32 * W at hf
  dsimp only [window, profile]
  omega

theorem source_data {n : ℕ} (W : ℕ) (budget : ℚ) (chosen : Fin n) :
    (run id W (callback W budget chosen)).1.data = (GeneralPaperEqualBitVertex.run W budget chosen).1.data := rfl

theorem source_work {n : ℕ} (W : ℕ) (budget : ℚ) (chosen : Fin n) :
    (GeneralPaperEqualBitVertex.run W budget chosen).2 =
      (run id W (callback W budget chosen)).2 + 64 * W + 64 := rfl

end Blotto.GeneralPaperEqualBitVertexLifetime
