import Blotto.GeneralPaperNativeCircleControlDraw

/-! Native priced stable sorting of representative references. Rational
values are loaded once per comparison and original index breaks ties. The
sort constructs its doubling depth; it uses no encoding-length primitive. -/
namespace Blotto.GeneralPaperNativeRepresentativeSort
open GeneralPaperRowSort
set_option autoImplicit false
set_option maxHeartbeats 2000000

def compare {R : ℕ} (price index : ℕ → ℕ) (A : ℕ) (values : FixedArrayTable R ℚ) (a b : Fin R) : Bool × ℕ :=
  let x := values.read a
  let y := values.read b
  (decide (x<y ∨ x=y ∧ a≤b),
    2*price (RationalExpression.pairWidth x y)+8*index (binaryWordWidth (a.val+1))+
      8*index (binaryWordWidth (b.val+1))+64*A)

theorem compare_data {R : ℕ} (price index : ℕ → ℕ) (A : ℕ) (values : FixedArrayTable R ℚ) (a b : Fin R) :
    (compare price index A values a b).1=decide (Before values.read a b) := rfl

theorem compare_work {R : ℕ} (price index : ℕ → ℕ) (hMono : Monotone price) (A H : ℕ)
    (values : FixedArrayTable R ℚ) (hValues : ∀ j,rationalWordWidth (values.read j)≤H)
    (hIndex : ∀ i≤R,index (binaryWordWidth (i+1))≤A) (a b : Fin R) :
    (compare price index A values a b).2≤2*price H+80*A := by
  have hp := hMono (max_le (hValues a) (hValues b))
  change price (RationalExpression.pairWidth (values.read a) (values.read b))≤price H at hp
  have ha := hIndex a.val a.isLt.le
  have hb := hIndex b.val b.isLt.le
  unfold compare
  dsimp only
  omega

def run {R : ℕ} (price index : ℕ → ℕ) (A : ℕ) (values : FixedArrayTable R ℚ) : FixedArrayTable R (Fin R) × ℕ :=
  let sorted := GeneralPaperPricedSort.run (compare price index A values) A (List.finRange R)
  let stored := PaperListReferenceArray.run index A sorted.1
  (⟨stored.1,by rw [PaperListReferenceArray.size,GeneralPaperPricedSort.length,List.length_finRange]⟩,
    sorted.2+stored.2+(16*R+16)*A)

theorem data {R : ℕ} (price index : ℕ → ℕ) (A : ℕ) (values : FixedArrayTable R ℚ) :
    (run price index A values).1=GeneralPaperRowSort.order values := by
  unfold run GeneralPaperRowSort.order
  dsimp only
  congr 1
  rw [PaperListReferenceArray.data,GeneralPaperPricedSort.data]
  simp_rw [compare_data]
  rfl

def profile (R A P : ℕ) : ℕ := GeneralPaperPricedSort.profile R A (2*P+80*A)+80*(R+1)*A

theorem work {R : ℕ} (price index : ℕ → ℕ) (hMono : Monotone price) (A H : ℕ) (hA : 1≤A)
    (values : FixedArrayTable R ℚ) (hValues : ∀ j,rationalWordWidth (values.read j)≤H)
    (hIndex : ∀ i≤R,index (binaryWordWidth (i+1))≤A) :
    (run price index A values).2≤profile R A (price H) := by
  have hSort := GeneralPaperPricedSort.work (compare price index A values) A (2*price H+80*A) (List.finRange R)
    (fun a _ b _ => compare_work price index hMono A H values hValues hIndex a b)
  have hList := GeneralPaperControlArrayPrice.list_work index A
    (GeneralPaperPricedSort.run (compare price index A values) A (List.finRange R)).1 hA
    (by simpa only [GeneralPaperPricedSort.length,List.length_finRange] using hIndex)
  rw [GeneralPaperPricedSort.length,List.length_finRange] at hList
  rw [List.length_finRange] at hSort
  change (GeneralPaperPricedSort.run (compare price index A values) A (List.finRange R)).2+
    (PaperListReferenceArray.run index A (GeneralPaperPricedSort.run (compare price index A values) A (List.finRange R)).1).2+
      (16*R+16)*A≤_
  unfold profile
  nlinarith only [hSort,hList]

end Blotto.GeneralPaperNativeRepresentativeSort
