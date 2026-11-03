import Blotto.GeneralPaperCellRepresentativePrice

/-! A constant-callback native array counter is formed once. Only the
literal multiplication/addition are priced; no array traversal is added.
-/
namespace Blotto.GeneralPaperClosedArrayCounterPrice
open GeneralPaperSignedCutOperands (magnitude width)
set_option autoImplicit false
set_option maxHeartbeats 6000000

def run (price : ℕ → ℕ) (slope count offset : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) slope count+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) (slope*count) offset

theorem work (price : ℕ → ℕ) (hMono : Monotone price) (slope count offset U : ℕ)
    (hSlope : slope≤128) (hOffset : offset≤256) : run price slope count offset≤4*price (width count U) := by
  have hMul := Nat.mul_le_mul_right count hSlope
  have hCount : count≤magnitude count U := by unfold magnitude; omega
  have hS : slope≤magnitude count U := by unfold magnitude; omega
  have hO : offset≤magnitude count U := by unfold magnitude; omega
  have hP : slope*count≤magnitude count U := by unfold magnitude; omega
  have hR : slope*count+offset≤magnitude count U := by unfold magnitude; omega
  have hW := GeneralPaperSignedCutOperands.word_bound count U
  have p (op : ℕ → ℕ → ℕ) (a b : ℕ) (ha : a≤magnitude count U) (hb : b≤magnitude count U) (hc : op a b≤magnitude count U) :
      GeneralPaperNaturalPrimitivePrice.binary price op a b≤2*price (width count U) :=
    (GeneralPaperNaturalPrimitivePrice.binary_le price hMono op a b (magnitude count U) ha hb hc).trans
      (Nat.mul_le_mul_left 2 (hMono hW))
  have ha := p (fun a b => a*b) slope count hS hCount hP
  have hb := p (fun a b => a+b) (slope*count) offset hP hO hR
  unfold run
  omega

end Blotto.GeneralPaperClosedArrayCounterPrice
