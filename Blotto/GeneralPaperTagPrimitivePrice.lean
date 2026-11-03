import Blotto.GeneralPaperNativeGridQueryPrice

/-! Exact threshold/any-open operations. A literal lexicographic test uses
at most two rational comparisons and one Boolean comparison. Addition uses
one rational addition and Boolean OR; no physical shift is introduced. -/
namespace Blotto.GeneralPaperTagPrimitivePrice
open GeneralPaperResponseTag
set_option autoImplicit false
set_option maxHeartbeats 5000000

def leValue (a b : Tag) : Bool :=
  if a.threshold<b.threshold then true
  else if a.threshold=b.threshold then !a.opened||b.opened else false

def le (price : ℕ → ℕ) (W : ℕ) (a b : Tag) : Bool × ℕ :=
  (leValue a b,2*price (RationalExpression.pairWidth a.threshold b.threshold)+64*W)

def add (price : ℕ → ℕ) (W : ℕ) (a b : Tag) : Tag × ℕ :=
  (⟨a.threshold+b.threshold,a.opened||b.opened⟩,
    GeneralPaperRationalPrimitivePrice.binary price (fun a b => a+b) a.threshold b.threshold+64*W)

theorem le_data (price : ℕ → ℕ) (W : ℕ) (a b : Tag) : (le price W a b).1=decide (a≤b) := by
  by_cases hl : a.threshold<b.threshold
  · have h := (le_iff a b).mpr (Or.inl hl)
    simp only [le,leValue,hl,ite_true,h,decide_true]
  · by_cases he : a.threshold=b.threshold
    · cases ha : a.opened <;> cases hb : b.opened <;> simp [le,leValue,le_iff,he,ha,hb]
    · have h : ¬a≤b := by rw [le_iff]; simp only [hl,he,false_and,or_self,not_false_eq_true]
      simp only [le,leValue,hl,he,ite_false,h,decide_false]

theorem add_data (price : ℕ → ℕ) (W : ℕ) (a b : Tag) : (add price W a b).1=a+b := rfl

theorem le_work (price : ℕ → ℕ) (hMono : Monotone price) (W L : ℕ) (a b : Tag)
    (ha : rationalWordWidth a.threshold≤L) (hb : rationalWordWidth b.threshold≤L) :
    (le price W a b).2≤2*price L+64*W := by
  have h := hMono (max_le ha hb)
  change 2*price (max (rationalWordWidth a.threshold) (rationalWordWidth b.threshold))+64*W≤_
  omega

theorem add_work (price : ℕ → ℕ) (hMono : Monotone price) (W L : ℕ) (a b : Tag)
    (ha : rationalWordWidth a.threshold≤L) (hb : rationalWordWidth b.threshold≤L)
    (hc : rationalWordWidth (a.threshold+b.threshold)≤L) : (add price W a b).2≤2*price L+64*W :=
  Nat.add_le_add_right (GeneralPaperRationalPrimitivePrice.binary_le price hMono (fun a b => a+b) _ _ L ha hb hc) _

theorem le_arithmetic (a b : Tag) : (le (fun _ => 1) 1 a b).2=66 := rfl

theorem add_arithmetic (a b : Tag) : (add (fun _ => 1) 1 a b).2=66 := rfl

end Blotto.GeneralPaperTagPrimitivePrice
