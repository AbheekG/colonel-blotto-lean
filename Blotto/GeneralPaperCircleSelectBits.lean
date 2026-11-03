import Blotto.GeneralPaperNativeDyadicBlocksBits

/-! Priced native first-boundary/second-lap circle index selection. Branch
tests and reached subtraction/result copies are explicit; no division or
circle-index oracle is used. Magnitude caps are erased proof bounds. -/
namespace Blotto.GeneralPaperCircleSelectBits
set_option autoImplicit false
set_option maxHeartbeats 3500000

def run (price : ℕ → ℕ) (A R D left right a : ℕ) : ℕ×ℕ :=
  let boundary := 2*D
  let common := GeneralPaperNaturalPrimitivePrice.binary price (fun x y => x*y) 2 D+
    GeneralPaperIntegerWordPrice.compare price left boundary+GeneralPaperIntegerWordPrice.compare price boundary right
  if left<boundary ∧ boundary<right then
    (0,common+price (GeneralPaperNaturalPrimitivePrice.word 0)+32*A) else
  if a<R then (a,common+GeneralPaperIntegerWordPrice.compare price a R+price (GeneralPaperNaturalPrimitivePrice.word a)+48*A) else
    let selected := a-R
    (selected,common+GeneralPaperIntegerWordPrice.compare price a R+
      GeneralPaperNaturalPrimitivePrice.binary price (fun x y => x-y) a R+
      price (GeneralPaperNaturalPrimitivePrice.word selected)+48*A)

theorem data (price : ℕ → ℕ) (A R D left right a : ℕ) :
    (run price A R D left right a).1=GeneralPaperCircleUnrolledChoice.select R D left right a := by
  simp only [run,GeneralPaperCircleUnrolledChoice.select]
  split
  · rfl
  · split <;> rfl

theorem work (price : ℕ → ℕ) (hMono : Monotone price) (A R D left right a M : ℕ)
    (hM : 2≤M) (hR : R≤M) (hD : 2*D≤M) (hLeft : left≤M) (hRight : right≤M) (hA : a≤M) :
    (run price A R D left right a).2≤48*A+8*price (1+binaryWordWidth M) := by
  let P := price (1+binaryWordWidth M)
  have hb := GeneralPaperNaturalPrimitivePrice.binary_le price hMono
  have hMult := hb (fun x y => x*y) 2 D M hM (by omega) hD
  have hSub := hb (fun x y => x-y) a R M hA hR (by omega)
  have hCmp (x y : ℕ) (hx : x≤M) (hy : y≤M) : GeneralPaperIntegerWordPrice.compare price x y≤P :=
    GeneralPaperIntegerWordPrice.compare_le price hMono x y (1+binaryWordWidth M)
      (Nat.add_le_add_left (binaryWordWidth_mono hx) 1) (Nat.add_le_add_left (binaryWordWidth_mono hy) 1)
  have h1 := hCmp left (2*D) hLeft hD
  have h2 := hCmp (2*D) right hD hRight
  have h3 := hCmp a R hA hR
  have hCopy (x : ℕ) (hx : x≤M) : price (GeneralPaperNaturalPrimitivePrice.word x)≤P :=
    hMono (Nat.add_le_add_left (binaryWordWidth_mono hx) 1)
  have hc0 := hCopy 0 (Nat.zero_le M)
  have hca := hCopy a hA
  have hcs := hCopy (a-R) (by omega)
  simp only [run]
  split
  · omega
  · split <;> omega

end Blotto.GeneralPaperCircleSelectBits
