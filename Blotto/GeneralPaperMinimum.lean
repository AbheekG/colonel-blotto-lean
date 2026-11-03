import Blotto.GeneralPaperStrictScore

/-! A streaming least-cost selector. It keeps one actual witness and uses
only rational cost comparisons; the predicates below are erased semantics.
The left witness wins a cost tie, fixing deterministic choices.
-/
namespace Blotto.GeneralPaperMinimum
set_option autoImplicit false

structure Selection (K : ℕ) where
  cost : ℚ
  labels : List (Fin K)

def pick {K : ℕ} : Option (Selection K) → Option (Selection K) → Option (Selection K)
  | none,b => b
  | a,none => a
  | some a,some b => if a.cost ≤ b.cost then some a else some b

def Best {K : ℕ} (possible : Selection K → Prop) : Option (Selection K) → Prop
  | none => ∀ x,¬possible x
  | some chosen => possible chosen ∧ ∀ x,possible x → chosen.cost ≤ x.cost

theorem pick_best {K : ℕ} (P Q : Selection K → Prop) (a b : Option (Selection K))
    (ha : Best P a) (hb : Best Q b) : Best (fun x => P x ∨ Q x) (pick a b) := by
  cases a with
  | none =>
    cases b with
    | none => exact fun x hx => hx.elim (ha x) (hb x)
    | some b =>
      refine ⟨Or.inr hb.1,?_⟩
      intro x hx
      exact hx.elim (fun h => (ha x h).elim) (hb.2 x)
  | some a =>
    cases b with
    | none =>
      refine ⟨Or.inl ha.1,?_⟩
      intro x hx
      exact hx.elim (ha.2 x) (fun h => (hb x h).elim)
    | some b =>
      change Best _ (if a.cost ≤ b.cost then some a else some b)
      split
      · rename_i hab
        refine ⟨Or.inl ha.1,?_⟩
        intro x hx
        exact hx.elim (ha.2 x) (fun h => hab.trans (hb.2 x h))
      · rename_i hab
        refine ⟨Or.inr hb.1,?_⟩
        intro x hx
        exact hx.elim (fun h => (le_of_not_ge hab).trans (ha.2 x h)) (hb.2 x)

def scan {α : Type*} {K : ℕ} (evaluate : α → Option (Selection K)) : List α → Option (Selection K)
  | [] => none
  | a::rest => pick (evaluate a) (scan evaluate rest)

theorem scan_best {α : Type*} {K : ℕ} (evaluate : α → Option (Selection K))
    (possible : α → Selection K → Prop) (xs : List α)
    (h : ∀ a ∈ xs,Best (possible a) (evaluate a)) :
    Best (fun x => ∃ a ∈ xs,possible a x) (scan evaluate xs) := by
  induction xs with
  | nil => intro x hx; simpa using hx
  | cons a rest ih =>
    have ha := h a (by simp)
    have hr := ih (fun b hb => h b (by simp [hb]))
    have hh := pick_best (possible a) (fun x => ∃ b ∈ rest,possible b x) _ _ ha hr
    have he : (fun x => possible a x ∨ ∃ b ∈ rest,possible b x)=
        (fun x => ∃ b ∈ a::rest,possible b x) := by
      funext x
      apply propext
      simp
    rw [he] at hh
    exact hh

def extend {K : ℕ} (label : Fin K) (cost : ℚ) (rest : Selection K) : Selection K :=
  ⟨cost+rest.cost,label::rest.labels⟩

end Blotto.GeneralPaperMinimum
