import Blotto.GeneralPaperBasisScatterBits

/-! Literal forward coordinate mapping with bit-priced K-1, field-offset
multiplication and label addition. The inverse exists only in erased proofs;
no quotient/modulus or dense scan is executed for each sparse coefficient.
-/
namespace Blotto.GeneralPaperBasisCoordinateBits
open RationalOrderCell GeneralPaperBasisCoordinates GeneralPaperNaturalPrimitivePrice
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem operands {m K : ℕ} (v : Variable m K) :
    K≤m*(K-1)+1 ∧ v.1.val≤m*(K-1)+1 ∧ K-1≤m*(K-1)+1 ∧ v.2.val≤m*(K-1)+1 ∧
      v.1.val*(K-1)≤m*(K-1)+1 ∧ v.1.val*(K-1)+v.2.val≤m*(K-1)+1 := by
  have hSum : v.1.val*(K-1)+v.2.val<m*(K-1) := (index v).isLt
  have hK : 1≤K-1 := by have hh := v.2.isLt; omega
  have hm : 1≤m := by have hh := v.1.isLt; omega
  have hField : v.1.val≤v.1.val*(K-1) := by nlinarith only [hK]
  have hLabels : K-1≤m*(K-1) := by nlinarith only [hm]
  omega

def scalar {m K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (v : Variable m K) : Fin (m*(K-1)) × ℕ :=
  (index v,24*W+binary primitive (fun a b => a-b) K 1+
    binary primitive (fun a b => a*b) v.1.val (K-1)+binary primitive (fun a b => a+b) (v.1.val*(K-1)) v.2.val)

theorem scalar_work {m K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W : ℕ) (v : Variable m K) :
    (scalar primitive W v).2≤24*W+6*primitive (1+binaryWordWidth (m*(K-1)+1)) := by
  have h := operands v
  have hSub := binary_le primitive hMono (fun a b => a-b) K 1 _ h.1 (by omega) h.2.2.1
  have hMul := binary_le primitive hMono (fun a b => a*b) v.1.val (K-1) _ h.2.1 h.2.2.1 h.2.2.2.2.1
  have hAdd := binary_le primitive hMono (fun a b => a+b) (v.1.val*(K-1)) v.2.val _ h.2.2.2.2.1 h.2.2.2.1 h.2.2.2.2.2
  dsimp only [scalar]
  omega

def run {m K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (terms : List (Variable m K × ℤ)) : List (Fin (m*(K-1)) × ℤ) × ℕ :=
  GeneralPaperPricedListMap.run W (fun t =>
    let packed := scalar primitive W t.1
    ((packed.1,t.2),packed.2+8*W)) terms

theorem data {m K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (terms : List (Variable m K × ℤ)) :
    (run primitive W terms).1=terms.map (fun t => (index t.1,t.2)) := by
  simp only [run,GeneralPaperPricedListMap.data,scalar]

theorem work {m K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W : ℕ) (terms : List (Variable m K × ℤ)) :
    (run primitive W terms).2≤terms.length*(40*W+6*primitive (1+binaryWordWidth (m*(K-1)+1)))+2*W := by
  have hh := GeneralPaperPricedListMap.work W (32*W+6*primitive (1+binaryWordWidth (m*(K-1)+1)))
    (fun t : Variable m K × ℤ => let packed := scalar primitive W t.1; ((packed.1,t.2),packed.2+8*W)) terms
    (by intro t _; have hp := scalar_work primitive hMono W t.1; change (scalar primitive W t.1).2+8*W≤_; omega)
  change (run primitive W terms).2≤_ at hh
  nlinarith only [hh]

end Blotto.GeneralPaperBasisCoordinateBits
