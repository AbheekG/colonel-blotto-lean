import Blotto.WordMachineLaw

/-! Carry proved invariants through a state-machine phase. Proof wrappers
are erased; the native transitions and numerator/denominator words are
unchanged. The output can then feed a typed continuation safely. -/

namespace Blotto

namespace WordChoiceTree

def map {α β : Type*} (f : α → β) : WordChoiceTree α → WordChoiceTree β
  | .leaf x => .leaf (f x)
  | .fork a b hb hab upper lower => .fork a b hb hab (upper.map f) (lower.map f)

theorem map_mean {α β : Type*} (T : WordChoiceTree α) (f : α → β) (g : β → ℝ) :
    (T.map f).decode.mean g = T.decode.mean (fun x => g (f x)) := by
  induction T with
  | leaf x => rfl
  | fork a b hb hab upper lower hu hl =>
    simp only [map, decode, AdaptiveChoiceTree.mean, hu, hl]

end WordChoiceTree

namespace WordTransition

def Postcondition {S α : Type*} (I : S → Prop) (P : α → Prop) : WordTransition S α → Prop
  | .done x => P x
  | .ask _ _ _ _ upper lower => I upper ∧ I lower

def RankProgress {S α : Type*} (rank : S → ℕ) (level : ℕ) : WordTransition S α → Prop
  | .done _ => True
  | .ask _ _ _ _ upper lower => rank upper < level ∧ rank lower < level

def restrict {S α : Type*} (I : S → Prop) (P : α → Prop) (t : WordTransition S α)
    (h : t.Postcondition I P) : WordTransition {s // I s} {x // P x} :=
  match t with
  | .done x => .done ⟨x, h⟩
  | .ask a b hb hab upper lower => .ask a b hb hab ⟨upper, h.1⟩ ⟨lower, h.2⟩

theorem restrict_progress {S α : Type*} (I : S → Prop) (P : α → Prop) (t : WordTransition S α)
    (h : t.Postcondition I P) (rank : S → ℕ) (level : ℕ)
    (hp : t.RankProgress rank level) :
    (t.restrict I P h).RankProgress (fun s => rank s.1) level := by
  cases t with
  | done x => trivial
  | ask a b hb hab upper lower => exact hp

theorem restrict_done {S α : Type*} (I : S → Prop) (P : α → Prop) (t : WordTransition S α)
    (h : t.Postcondition I P) (x : α) (he : t = .done x) :
    t.restrict I P h = .done ⟨x, by simpa only [he, Postcondition] using h⟩ := by
  cases he
  rfl

theorem restrict_ask {S α : Type*} (I : S → Prop) (P : α → Prop) (t : WordTransition S α)
    (h : t.Postcondition I P)
    (a b : ℕ) (hb : 0 < b) (hab : a ≤ b) (upper lower : S) (he : t = .ask a b hb hab upper lower) :
    t.restrict I P h = .ask a b hb hab
      ⟨upper, (by simpa only [he, Postcondition] using h : I upper ∧ I lower).1⟩
      ⟨lower, (by simpa only [he, Postcondition] using h : I upper ∧ I lower).2⟩ := by
  cases he
  rfl

end WordTransition

namespace WordStateMachine

def restricted {S α : Type*} (m : WordStateMachine S α) (I : S → Prop) (P : α → Prop)
    (hI : ∀ s, I s → (m.step s).Postcondition I P) : WordStateMachine {s // I s} {x // P x} where
  step := fun s => (m.step s.1).restrict I P (hI s.1 s.2)
  rank := fun s => m.rank s.1
  progress := by
    intro s
    exact WordTransition.restrict_progress I P (m.step s.1) (hI s.1 s.2) m.rank (m.rank s.1) (m.progress s.1)

theorem restricted_step {S α : Type*} (m : WordStateMachine S α) (I : S → Prop) (P : α → Prop)
    (hI : ∀ s, I s → (m.step s).Postcondition I P) (s : {s // I s}) :
    (m.restricted I P hI).step s = (m.step s.1).restrict I P (hI s.1 s.2) := rfl

theorem restricted_specification {S α : Type*} (m : WordStateMachine S α) (I : S → Prop) (P : α → Prop)
    (hI : ∀ s, I s → (m.step s).Postcondition I P) (s : {s // I s}) :
    ((m.restricted I P hI).specification s).map Subtype.val = m.specification s.1 := by
  have hAll : ∀ n, ∀ s : {s // I s}, m.rank s.1 = n →
      ((m.restricted I P hI).specification s).map Subtype.val = m.specification s.1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s he
      cases hs : m.step s.1 with
      | done x =>
        have hx : P x := by have h := hI s.1 s.2; rw [hs] at h; exact h
        have ht : (m.restricted I P hI).step s = .done ⟨x, hx⟩ := by
          rw [m.restricted_step]
          exact WordTransition.restrict_done I P (m.step s.1) (hI s.1 s.2) x hs
        conv_lhs => unfold specification
        rw [ht]
        conv_rhs => unfold specification
        rw [hs]
        rfl
      | ask a b hb hab upper lower =>
        have hp := m.progress s.1
        have hn := hI s.1 s.2
        rw [hs] at hp hn
        have ht : (m.restricted I P hI).step s = .ask a b hb hab ⟨upper, hn.1⟩ ⟨lower, hn.2⟩ := by
          rw [m.restricted_step]
          exact WordTransition.restrict_ask I P (m.step s.1) (hI s.1 s.2) a b hb hab upper lower hs
        conv_lhs => unfold specification
        rw [ht]
        conv_rhs => unfold specification
        rw [hs]
        simp only [WordChoiceTree.map]
        rw [ih (m.rank upper) (by omega) ⟨upper, hn.1⟩ rfl,
          ih (m.rank lower) (by omega) ⟨lower, hn.2⟩ rfl]
  exact hAll (m.rank s.1) s rfl

theorem restricted_mean {S α : Type*} (m : WordStateMachine S α) (I : S → Prop) (P : α → Prop)
    (hI : ∀ s, I s → (m.step s).Postcondition I P) (s : {s // I s}) (f : α → ℝ) :
    ((m.restricted I P hI).specification s).decode.mean (fun x => f x.1) = (m.specification s.1).decode.mean f := by
  rw [← WordChoiceTree.map_mean _ Subtype.val f, m.restricted_specification I P hI s]

end WordStateMachine
end Blotto
