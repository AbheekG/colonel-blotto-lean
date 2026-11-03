import Blotto.GeneralPaperNativeProfitOptimizer
import Mathlib.Data.Prod.Lex

/-! The paper's literal response resource tags: closed-threshold sum and
one any-open Boolean. Addition uses OR and order is lexicographic, closed
before open. No physical Delta shift occurs in arithmetic or comparisons.
-/
namespace Blotto.GeneralPaperResponseTag
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Tag where
  threshold : ℚ
  opened : Bool
  deriving DecidableEq

theorem tag_ext {a b : Tag} (hThreshold : a.threshold=b.threshold) (hOpened : a.opened=b.opened) : a=b := by
  cases a
  cases b
  cases hThreshold
  cases hOpened
  rfl

def key (a : Tag) : ℚ ×ₗ Bool := toLex (a.threshold,a.opened)

theorem key_injective : Function.Injective key := by
  intro a b h
  have he := toLex.injective h
  exact tag_ext (congrArg Prod.fst he) (congrArg Prod.snd he)

instance : LinearOrder Tag := LinearOrder.lift' key key_injective

instance : Zero Tag := ⟨⟨0,false⟩⟩

instance : Add Tag := ⟨fun a b => ⟨a.threshold+b.threshold,a.opened||b.opened⟩⟩

instance : AddCommMonoid Tag where
  zero := 0
  add := (·+·)
  nsmul := nsmulRec
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  add_assoc a b c := tag_ext (add_assoc a.threshold b.threshold c.threshold) (Bool.or_assoc a.opened b.opened c.opened)
  add_comm a b := tag_ext (add_comm a.threshold b.threshold) (Bool.or_comm a.opened b.opened)
  zero_add a := tag_ext (zero_add a.threshold) (by rfl)
  add_zero a := tag_ext (add_zero a.threshold) (by change (a.opened || false)=a.opened; cases a.opened <;> rfl)

theorem threshold_add (a b : Tag) : (a+b).threshold=a.threshold+b.threshold := rfl

theorem opened_add (a b : Tag) : (a+b).opened=(a.opened||b.opened) := rfl

theorem threshold_zero : (0:Tag).threshold=0 := rfl

theorem opened_zero : (0:Tag).opened=false := rfl

theorem bool_le_iff (a b : Bool) : a≤b ↔ a=false ∨ b=true := by cases a <;> cases b <;> decide

theorem le_iff (a b : Tag) : a≤b ↔ a.threshold<b.threshold ∨
    (a.threshold=b.threshold ∧ (a.opened=false ∨ b.opened=true)) := by
  change key a≤key b ↔ _
  simp only [key,Prod.Lex.toLex_le_toLex,bool_le_iff]

theorem add_monotone (a b : Tag) (h : a≤b) (c : Tag) : a+c≤b+c := by
  rcases (le_iff a b).mp h with hLt|⟨hEq,hFlag⟩
  · exact (le_iff _ _).mpr (Or.inl (show a.threshold+c.threshold<b.threshold+c.threshold by linarith only [hLt]))
  · apply (le_iff _ _).mpr
    right
    refine ⟨congrArg (fun x => x+c.threshold) hEq,?_⟩
    simp only [opened_add]
    cases ha : a.opened <;> cases hb : b.opened <;> cases hc : c.opened <;> simp_all

instance : IsOrderedAddMonoid Tag where
  add_le_add_left a b h c := add_monotone a b h c

def budget (B : ℚ) : Tag := ⟨B,false⟩

theorem feasible_iff (a : Tag) (B : ℚ) : a≤budget B ↔ a.threshold<B ∨ (a.threshold=B ∧ a.opened=false) := by
  rw [le_iff]
  simp only [budget,Bool.false_eq_true,or_false]

theorem closed_order (a b : ℚ) : (⟨a,false⟩:Tag)≤⟨b,false⟩ ↔ a≤b := by
  rw [le_iff]
  simp only [true_or,and_true]
  constructor
  · rintro (h|h) <;> linarith
  · intro h
    by_cases he : a<b
    · exact Or.inl he
    · exact Or.inr (by linarith)

theorem budget_nonnegative (B : ℚ) (hB : 0≤B) : (0:Tag)≤budget B :=
  (closed_order 0 B).mpr hB

theorem open_at_budget (B : ℚ) : ¬(⟨B,true⟩:Tag)≤budget B := by
  rw [feasible_iff]
  simp

end Blotto.GeneralPaperResponseTag
