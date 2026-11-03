import Blotto.GeneralPaperCDFShiftPrice

/-! Fixed native preparation sums. Each addition charges input and result
words; callers derive the whole-sum cap from their actual native result.
These formulas are erased prices, not additional source traversals.
-/
namespace Blotto.GeneralPaperFieldPlanCounters
set_option autoImplicit false

def pair (price : ℕ → ℕ) (a b : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) a b+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) (a+b) 16

def triple (price : ℕ → ℕ) (a b c : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) a b+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) (a+b) c+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) (a+b+c) 16

theorem binary_work (price : ℕ → ℕ) (hMono : Monotone price) (M L a b : ℕ)
    (hW : 1+binaryWordWidth M≤L) (hSum : a+b≤M) :
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a+b) a b≤2*price L :=
  (GeneralPaperNaturalPrimitivePrice.binary_le price hMono _ a b M (by omega) (by omega) hSum).trans
    (Nat.mul_le_mul_left 2 (hMono hW))

theorem pair_work (price : ℕ → ℕ) (hMono : Monotone price) (M L a b : ℕ)
    (hW : 1+binaryWordWidth M≤L) (hSum : a+b+16≤M) : pair price a b≤4*price L := by
  have ha := binary_work price hMono M L a b hW (by omega)
  have hb := binary_work price hMono M L (a+b) 16 hW hSum
  unfold pair
  omega

theorem triple_work (price : ℕ → ℕ) (hMono : Monotone price) (M L a b c : ℕ)
    (hW : 1+binaryWordWidth M≤L) (hSum : a+b+c+16≤M) : triple price a b c≤6*price L := by
  have ha := binary_work price hMono M L a b hW (by omega)
  have hb := binary_work price hMono M L (a+b) c hW (by omega)
  have hc := binary_work price hMono M L (a+b+c) 16 hW hSum
  unfold triple
  omega

theorem four_work (price : ℕ → ℕ) (hMono : Monotone price) (M L a b c d : ℕ)
    (hW : 1+binaryWordWidth M≤L) (hSum : a+b+c+d+16≤M) :
    GeneralPaperSignedTailOperands.additions price a b c d≤8*price L := by
  have ha := binary_work price hMono M L a b hW (by omega)
  have hb := binary_work price hMono M L (a+b) c hW (by omega)
  have hc := binary_work price hMono M L (a+b+c) d hW (by omega)
  have hd := binary_work price hMono M L (a+b+c+d) 16 hW hSum
  unfold GeneralPaperSignedTailOperands.additions
  omega

end Blotto.GeneralPaperFieldPlanCounters
