import Blotto.GeneralPaperPricedSort

/-! The filtering and duplicate-removal traversals around crossing sorting.
Rational comparisons pay their actual operand width under Rat; the other
charges are reference/control words. No rational payload is copied by cons.
-/
namespace Blotto.GeneralPaperPricedCrossingPasses
set_option autoImplicit false
set_option maxHeartbeats 2500000

def leRun (primitive : ℕ → ℕ) (a b : ℚ) : Bool × ℕ :=
  (decide (a≤b),primitive (RationalExpression.pairWidth a b))

theorem le_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (a b : ℚ) (H : ℕ)
    (ha : rationalWordWidth a≤H) (hb : rationalWordWidth b≤H) :
    (leRun primitive a b).2≤primitive H := hMono (max_le ha hb)

def filterRun (primitive : ℕ → ℕ) (W : ℕ) (lo hi : ℚ) : List ℚ → List ℚ × ℕ
  | [] => ([],2*W)
  | x::rest =>
    let later := filterRun primitive W lo hi rest
    (if lo≤x ∧ x≤hi then x::later.1 else later.1,
      later.2+(leRun primitive lo x).2+(leRun primitive x hi).2+16*W)

theorem filter_data (primitive : ℕ → ℕ) (W : ℕ) (lo hi : ℚ) (xs : List ℚ) :
    (filterRun primitive W lo hi xs).1=xs.filter (fun t => decide (lo≤t ∧ t≤hi)) := by
  induction xs with
  | nil => rfl
  | cons x rest ih => simp only [filterRun,List.filter_cons,ih]; split <;> simp_all

theorem filter_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W H : ℕ) (lo hi : ℚ) (xs : List ℚ)
    (hl : rationalWordWidth lo≤H) (hh : rationalWordWidth hi≤H)
    (h : ∀ x∈xs,rationalWordWidth x≤H) :
    (filterRun primitive W lo hi xs).2≤(2*primitive H+16*W)*xs.length+2*W := by
  induction xs with
  | nil => simp only [filterRun,List.length_nil,Nat.mul_zero,Nat.zero_add,le_refl]
  | cons x rest ih =>
    have hr := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have ha := le_work primitive hMono lo x H hl (h x List.mem_cons_self)
    have hb := le_work primitive hMono x hi H (h x List.mem_cons_self) hh
    change (filterRun primitive W lo hi rest).2+(leRun primitive lo x).2+(leRun primitive x hi).2+16*W≤_
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

def afterRun (primitive : ℕ → ℕ) (W : ℕ) (last : ℚ) : List ℚ → List ℚ × ℕ
  | [] => ([],2*W)
  | x::rest =>
    if x=last then
      let later := afterRun primitive W last rest
      (later.1,later.2+primitive (RationalExpression.pairWidth x last)+16*W)
    else
      let later := afterRun primitive W x rest
      (x::later.1,later.2+primitive (RationalExpression.pairWidth x last)+16*W)

theorem after_data (primitive : ℕ → ℕ) (W : ℕ) (last : ℚ) (xs : List ℚ) :
    (afterRun primitive W last xs).1=GeneralPaperRaySortedCrossings.after last xs := by
  induction xs generalizing last with
  | nil => rfl
  | cons x rest ih => simp only [afterRun,GeneralPaperRaySortedCrossings.after]; split <;> simp only [ih]

theorem after_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W H : ℕ) (last : ℚ) (xs : List ℚ)
    (hl : rationalWordWidth last≤H) (h : ∀ x∈xs,rationalWordWidth x≤H) :
    (afterRun primitive W last xs).2≤(primitive H+16*W)*xs.length+2*W := by
  induction xs generalizing last with
  | nil => simp only [afterRun,List.length_nil,Nat.mul_zero,Nat.zero_add,le_refl]
  | cons x rest ih =>
    have hx := h x List.mem_cons_self
    have hc := hMono (max_le hx hl)
    change primitive (RationalExpression.pairWidth x last)≤primitive H at hc
    have ht : ∀ y∈rest,rationalWordWidth y≤H := fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [afterRun]
    split
    · have hr := ih last hl ht
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
      omega
    · have hr := ih x hx ht
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
      omega

def uniqueRun (primitive : ℕ → ℕ) (W : ℕ) : List ℚ → List ℚ × ℕ
  | [] => ([],2*W)
  | x::rest =>
    let later := afterRun primitive W x rest
    (x::later.1,later.2+8*W)

theorem unique_data (primitive : ℕ → ℕ) (W : ℕ) (xs : List ℚ) :
    (uniqueRun primitive W xs).1=GeneralPaperRaySortedCrossings.unique xs := by
  cases xs <;> simp only [uniqueRun,GeneralPaperRaySortedCrossings.unique,after_data]

theorem unique_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W H : ℕ) (xs : List ℚ)
    (h : ∀ x∈xs,rationalWordWidth x≤H) :
    (uniqueRun primitive W xs).2≤(primitive H+16*W)*xs.length+2*W := by
  cases xs with
  | nil => simp only [uniqueRun,List.length_nil,Nat.mul_zero,Nat.zero_add,le_refl]
  | cons x rest =>
    have hr := after_work primitive hMono W H x rest (h x List.mem_cons_self)
      (fun y hy => h y (List.mem_cons_of_mem _ hy))
    change (afterRun primitive W x rest).2+8*W≤_
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

end Blotto.GeneralPaperPricedCrossingPasses
