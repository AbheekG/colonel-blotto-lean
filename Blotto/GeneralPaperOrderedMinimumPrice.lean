import Blotto.GeneralPaperTagHeight

/-! Preserve the native earlier-predecessor tie rule. Only a comparison of
two present tags executes; absent cases return the existing reference. -/
namespace Blotto.GeneralPaperOrderedMinimumPrice
open GeneralPaperResponseTag GeneralPaperOrderedMinimum
set_option autoImplicit false
set_option maxHeartbeats 5000000

def run {Witness : Type*} (price : ℕ → ℕ) (W : ℕ) :
    Option (Selection Tag Witness) → Option (Selection Tag Witness) → Option (Selection Tag Witness) × ℕ
  | none,b => (b,64*W)
  | a,none => (a,64*W)
  | some a,some b =>
    let compared := GeneralPaperTagPrimitivePrice.le price W a.cost b.cost
    (if compared.1 then some a else some b,compared.2+64*W)

def Safe {Witness : Type*} (s : ℕ) (value : Option (Selection Tag Witness)) : Prop :=
  ∀ chosen,value=some chosen → RationalHeight chosen.cost.threshold s

theorem data {Witness : Type*} (price : ℕ → ℕ) (W : ℕ) (a b : Option (Selection Tag Witness)) :
    (run price W a b).1=pick a b := by
  cases a with
  | none => rfl
  | some a =>
    cases b with
    | none => rfl
    | some b =>
      simp only [run,GeneralPaperTagPrimitivePrice.le_data]
      by_cases h : a.cost≤b.cost <;> simp only [pick,h,decide_true,decide_false,ite_true,ite_false,Bool.false_eq_true]

theorem pick_safe {Witness : Type*} (s : ℕ) (a b : Option (Selection Tag Witness)) (ha : Safe s a) (hb : Safe s b) :
    Safe s (pick a b) := by
  cases a with
  | none => exact hb
  | some a =>
    cases b with
    | none => exact ha
    | some b =>
      change Safe s (if a.cost≤b.cost then some a else some b)
      split <;> assumption

theorem safe {Witness : Type*} (price : ℕ → ℕ) (W s : ℕ) (a b : Option (Selection Tag Witness))
    (ha : Safe s a) (hb : Safe s b) : Safe s (run price W a b).1 := by
  rw [data]
  exact pick_safe s a b ha hb

theorem work {Witness : Type*} (price : ℕ → ℕ) (hMono : Monotone price) (W s : ℕ)
    (a b : Option (Selection Tag Witness)) (ha : Safe s a) (hb : Safe s b) :
    (run price W a b).2≤2*price (1+2*s)+128*W := by
  cases a with
  | none => change 64*W≤_; omega
  | some a =>
    cases b with
    | none => change 64*W≤_; omega
    | some b =>
      have h := GeneralPaperTagPrimitivePrice.le_work price hMono W (1+2*s) a.cost b.cost
        (rationalWordWidth_of_height (ha a rfl)) (rationalWordWidth_of_height (hb b rfl))
      change (GeneralPaperTagPrimitivePrice.le price W a.cost b.cost).2+64*W≤_
      omega

theorem arithmetic_work {Witness : Type*} (a b : Option (Selection Tag Witness)) :
    (run (fun _ => 1) 1 a b).2≤130 := by
  cases a <;> cases b <;> norm_num [run,GeneralPaperTagPrimitivePrice.le]

end Blotto.GeneralPaperOrderedMinimumPrice
