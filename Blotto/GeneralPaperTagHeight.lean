import Blotto.GeneralPaperTagPrimitivePrice

/-! A height profile follows the actual balanced resource additions.
It grows like 2^h times the leaf height, rather than assigning a uniformly
short word to exact sums of unrelated catalogue denominators. -/
namespace Blotto.GeneralPaperTagHeight
open GeneralPaperResponseTag
set_option autoImplicit false
set_option maxHeartbeats 5000000

def word (s height : ℕ) : ℕ := 1+2*expressionHeightBudget s height

theorem word_zero (s : ℕ) : word s 0=1+2*s := by rw [word,expressionHeightBudget_zero]

theorem word_mono (s h H : ℕ) (hh : h≤H) : word s h≤word s H :=
  Nat.add_le_add_left (Nat.mul_le_mul_left 2 (expressionHeightBudget_mono s hh)) 1

theorem zero_height (s : ℕ) (hs : 0<s) : RationalHeight (0:Tag).threshold s := by
  change RationalHeight (0:ℚ) s
  constructor
  · simp only [Rat.num_zero,Int.natAbs_zero]; exact Nat.two_pow_pos s
  · simp only [Rat.den_zero]
    exact (Nat.one_lt_two_pow_iff).mpr (by omega)

theorem add_height (s h : ℕ) (a b : Tag)
    (ha : RationalHeight a.threshold (expressionHeightBudget s h))
    (hb : RationalHeight b.threshold (expressionHeightBudget s h)) :
    RationalHeight (a+b).threshold (expressionHeightBudget s (h+1)) := by
  rw [threshold_add,expressionHeightBudget_succ]
  simpa only [two_mul] using ha.add hb

theorem le_work (price : ℕ → ℕ) (hMono : Monotone price) (W s h : ℕ) (a b : Tag)
    (ha : RationalHeight a.threshold (expressionHeightBudget s h))
    (hb : RationalHeight b.threshold (expressionHeightBudget s h)) :
    (GeneralPaperTagPrimitivePrice.le price W a b).2≤2*price (word s h)+64*W :=
  GeneralPaperTagPrimitivePrice.le_work price hMono W _ a b (rationalWordWidth_of_height ha) (rationalWordWidth_of_height hb)

theorem add_work (price : ℕ → ℕ) (hMono : Monotone price) (W s h : ℕ) (a b : Tag)
    (ha : RationalHeight a.threshold (expressionHeightBudget s h))
    (hb : RationalHeight b.threshold (expressionHeightBudget s h)) :
    (GeneralPaperTagPrimitivePrice.add price W a b).2≤2*price (word s (h+1))+64*W :=
  GeneralPaperTagPrimitivePrice.add_work price hMono W _ a b
    ((rationalWordWidth_of_height ha).trans (word_mono s h (h+1) (by omega)))
    ((rationalWordWidth_of_height hb).trans (word_mono s h (h+1) (by omega)))
    (rationalWordWidth_of_height (add_height s h a b ha hb))

theorem fraction_height (a : GeneralPaperCodeAlphabet.Alphabet) (f : Farey.Fraction)
    (hNum : f.num≤a.C) (hDen : f.den≤a.C) : RationalHeight f.value (a.lambda+1) := by
  have hC : a.C<2^a.lambda := by rw [←a.dyadic]; have := a.scalePositive; omega
  have hp := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show a.lambda≤a.lambda+1 by omega)
  exact RationalHeight.fraction (f.num:ℤ) f.den (a.lambda+1) f.den_pos
    (by simpa only [Int.natAbs_natCast] using (hNum.trans_lt hC).trans_le hp)
    ((hDen.trans_lt hC).trans_le hp)

theorem ready_height {m k : ℕ} (ready : GeneralPaperCatalogueOptimizer.Ready m k) (j : Fin m)
    (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) :
    RationalHeight ((ready.cached.read j).tags.read i).threshold (ready.alphabet.lambda+1) := by
  have hb := GeneralPaperCatalogueTagValue.native_bounds ready.alphabet ready.response k ready.summaries ready.data ready.data_spec j i
  rw [ready.cached_spec,GeneralPaperOrderedNativeProfitOptimizer.plans,FixedArrayTable.read_ofFn]
  change RationalHeight ((((GeneralPaperCatalogueArrays.tags ready.data).read j).read i).threshold) _
  simp only [GeneralPaperCatalogueArrays.tags,GeneralPaperNativeRowBudget.tags,FixedArrayTable.read_ofFn]
  exact fraction_height ready.alphabet _ hb.1 hb.2

end Blotto.GeneralPaperTagHeight
