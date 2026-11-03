import Blotto.GeneralPaperAffineValuePrice

/-! Price the actual affine minimum selector. Both expressions are evaluated
only in a present/present comparison; the earlier candidate still wins ties.
Candidates and selected values share references to their predecessor lists.
-/
namespace Blotto.GeneralPaperAffineMinimumPrice
open GeneralPaperRayAffine GeneralPaperRayAffineMinimum
set_option autoImplicit false
set_option maxHeartbeats 4000000

def Bounded {K : ℕ} (D E A B : ℕ) (value : Option (Choice K)) : Prop :=
  ∀ c,value=some c → GeneralPaperRayAffineBound.Bounded D E A B c.expression

def pickRun {K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (t : ℚ) :
    Option (Choice K) → Option (Choice K) → Option (Choice K) × ℕ
  | none,b => (b,8*W)
  | a,none => (a,8*W)
  | some a,some b =>
    let first := GeneralPaperAffineValuePrice.run primitive W a.expression t
    let second := GeneralPaperAffineValuePrice.run primitive W b.expression t
    (if first.1≤second.1 then some a else some b,
      first.2+second.2+8*W+primitive (RationalExpression.pairWidth first.1 second.1))

theorem pick_data {K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (t : ℚ) (a b : Option (Choice K)) :
    (pickRun primitive W t a b).1=GeneralPaperRayAffineMinimum.pick t a b := by
  cases a <;> cases b <;> rfl

theorem pick_bounded {K : ℕ} (primitive : ℕ → ℕ) (W D E A B : ℕ) (t : ℚ)
    (a b : Option (Choice K)) (ha : Bounded D E A B a) (hb : Bounded D E A B b) :
    Bounded D E A B (pickRun primitive W t a b).1 := by
  rw [pick_data]
  intro chosen hc
  rcases GeneralPaperRayAffineMinimum.pick_origin t a b chosen hc with h|h
  · exact ha chosen h
  · exact hb chosen h

theorem pick_work {K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W D E A B R s : ℕ) (hD : 0<D) (hE : 0<E)
    (hR : GeneralPaperRayAffineBound.rootWidth D E A B≤R) (t : ℚ) (ht : RationalHeight t s)
    (a b : Option (Choice K)) (ha : Bounded D E A B a) (hb : Bounded D E A B b) :
    (pickRun primitive W t a b).2≤40*W+9*primitive (1+2*(R+s+1)) := by
  cases a with
  | none => simp only [pickRun]; omega
  | some a =>
    cases b with
    | none => simp only [pickRun]; omega
    | some b =>
      have hFirst := GeneralPaperAffineValuePrice.work primitive hMono W D E A B R s hD hE
        a.expression (ha a rfl) hR t ht
      have hSecond := GeneralPaperAffineValuePrice.work primitive hMono W D E A B R s hD hE
        b.expression (hb b rfl) hR t ht
      have hHeight (f : Affine) (hf : GeneralPaperRayAffineBound.Bounded D E A B f) :
          RationalHeight (f.value t) (R+s+1) := by
        have hv := GeneralPaperRayAffineBound.value_height hD hE hf t ht
        apply hv.mono
        unfold GeneralPaperRayAffineBound.rootWidth at hR
        omega
      have hCompare := hMono (max_le (rationalWordWidth_of_height (hHeight a.expression (ha a rfl)))
        (rationalWordWidth_of_height (hHeight b.expression (hb b rfl))))
      change primitive (RationalExpression.pairWidth (a.expression.value t) (b.expression.value t))≤
        primitive (1+2*(R+s+1)) at hCompare
      change (GeneralPaperAffineValuePrice.run primitive W a.expression t).2+
        (GeneralPaperAffineValuePrice.run primitive W b.expression t).2+8*W+
          primitive (RationalExpression.pairWidth (a.expression.value t) (b.expression.value t))≤_
      omega

def scanRun {i : Type*} {K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (t : ℚ)
    (evaluate : i → Option (Choice K) × ℕ) : List i → Option (Choice K) × ℕ
  | [] => (none,2*W)
  | a::rest =>
    let current := evaluate a
    let later := scanRun primitive W t evaluate rest
    let selected := pickRun primitive W t current.1 later.1
    (selected.1,current.2+later.2+selected.2+4*W)

theorem scan_data {i : Type*} {K : ℕ} (primitive : ℕ → ℕ) (W : ℕ) (t : ℚ)
    (evaluate : i → Option (Choice K) × ℕ) (xs : List i) :
    (scanRun primitive W t evaluate xs).1=GeneralPaperRayAffineMinimum.scan t (fun a => (evaluate a).1) xs := by
  induction xs with
  | nil => rfl
  | cons a rest ih => simp only [scanRun,pick_data,GeneralPaperRayAffineMinimum.scan,ih]

theorem scan_bounded {i : Type*} {K : ℕ} (primitive : ℕ → ℕ) (W D E A B : ℕ) (t : ℚ)
    (evaluate : i → Option (Choice K) × ℕ) (xs : List i)
    (h : ∀ a∈xs,Bounded D E A B (evaluate a).1) :
    Bounded D E A B (scanRun primitive W t evaluate xs).1 := by
  rw [scan_data]
  intro chosen hc
  obtain ⟨a,ha,he⟩ := GeneralPaperRayAffineMinimum.scan_origin t (fun a => (evaluate a).1) xs chosen hc
  exact h a ha chosen he

theorem scan_work {i : Type*} {K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W D E A B R s C : ℕ) (hD : 0<D) (hE : 0<E)
    (hR : GeneralPaperRayAffineBound.rootWidth D E A B≤R) (t : ℚ) (ht : RationalHeight t s)
    (evaluate : i → Option (Choice K) × ℕ) (xs : List i)
    (hBound : ∀ a∈xs,Bounded D E A B (evaluate a).1) (hWork : ∀ a∈xs,(evaluate a).2≤C) :
    (scanRun primitive W t evaluate xs).2≤(C+44*W+9*primitive (1+2*(R+s+1)))*xs.length+2*W := by
  induction xs with
  | nil => simp only [scanRun,List.length_nil,Nat.mul_zero,Nat.zero_add,le_refl]
  | cons a rest ih =>
    have hr := ih (fun b hb => hBound b (List.mem_cons_of_mem _ hb)) (fun b hb => hWork b (List.mem_cons_of_mem _ hb))
    have hb := scan_bounded primitive W D E A B t evaluate rest (fun b hb => hBound b (List.mem_cons_of_mem _ hb))
    have hp := pick_work primitive hMono W D E A B R s hD hE hR t ht
      (evaluate a).1 (scanRun primitive W t evaluate rest).1 (hBound a List.mem_cons_self) hb
    have ha := hWork a List.mem_cons_self
    change (evaluate a).2+(scanRun primitive W t evaluate rest).2+
      (pickRun primitive W t (evaluate a).1 (scanRun primitive W t evaluate rest).1).2+4*W≤_
    simp only [List.length_cons]
    nlinarith only [hr,hp,ha]

end Blotto.GeneralPaperAffineMinimumPrice
