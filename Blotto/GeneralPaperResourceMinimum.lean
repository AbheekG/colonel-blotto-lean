import Blotto.GeneralPaperProfitGridCover

/-! An exact rational resource minimum with a typed predecessor payload.
Leaves will store an option index; internal states store two child indices.
No resource is rounded and equal costs keep the earlier predecessor.
-/
namespace Blotto.GeneralPaperResourceMinimum
set_option autoImplicit false

structure Selection (Witness : Type*) where
  cost : ℚ
  predecessor : Witness

def pick {Witness : Type*} : Option (Selection Witness) → Option (Selection Witness) → Option (Selection Witness)
  | none,b => b
  | a,none => a
  | some a,some b => if a.cost≤b.cost then some a else some b

def Best {Witness : Type*} (possible : Selection Witness → Prop) : Option (Selection Witness) → Prop
  | none => ∀ x, ¬possible x
  | some chosen => possible chosen ∧ ∀ x, possible x → chosen.cost≤x.cost

theorem pick_best {Witness : Type*} (P Q : Selection Witness → Prop) (a b : Option (Selection Witness))
    (ha : Best P a) (hb : Best Q b) : Best (fun x => P x ∨ Q x) (pick a b) := by
  cases a with
  | none =>
    cases b with
    | none => exact fun x hx => hx.elim (ha x) (hb x)
    | some b => exact ⟨Or.inr hb.1,fun x hx => hx.elim (fun h => (ha x h).elim) (hb.2 x)⟩
  | some a =>
    cases b with
    | none => exact ⟨Or.inl ha.1,fun x hx => hx.elim (ha.2 x) (fun h => (hb x h).elim)⟩
    | some b =>
      change Best _ (if a.cost≤b.cost then some a else some b)
      split
      · rename_i hab
        exact ⟨Or.inl ha.1,fun x hx => hx.elim (ha.2 x) (fun h => hab.trans (hb.2 x h))⟩
      · rename_i hab
        exact ⟨Or.inr hb.1,fun x hx => hx.elim (fun h => (le_of_not_ge hab).trans (ha.2 x h)) (hb.2 x)⟩

end Blotto.GeneralPaperResourceMinimum
