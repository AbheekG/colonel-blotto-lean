import Blotto.WordMachineMap

/-! Serial native control flow with output-dependent continuation states.
The runtime joins transitions at completion and shares the caller's bit cap;
no intermediate sampling call or tree construction occurs in a transition. -/

namespace Blotto

namespace WordChoiceTree

def bind {α β : Type*} (f : α → WordChoiceTree β) : WordChoiceTree α → WordChoiceTree β
  | .leaf x => f x
  | .fork a b hb hab upper lower => .fork a b hb hab (upper.bind f) (lower.bind f)

theorem bind_mean {α β : Type*} (T : WordChoiceTree α) (f : α → WordChoiceTree β) (g : β → ℝ) :
    (T.bind f).decode.mean g = T.decode.mean (fun x => (f x).decode.mean g) := by
  induction T with
  | leaf x => rfl
  | fork a b hb hab upper lower hu hl => simp only [bind, decode, AdaptiveChoiceTree.mean, hu, hl]

end WordChoiceTree

inductive SerialState (S α : Type*) (T : α → Type*) where
  | source (state : S)
  | continuation (value : α) (state : T value)

namespace WordTransition

def mapState {S T α : Type*} (f : S → T) : WordTransition S α → WordTransition T α
  | .done x => .done x
  | .ask a b hb hab upper lower => .ask a b hb hab (f upper) (f lower)

theorem mapState_progress {S T α : Type*} (f : S → T) (t : WordTransition S α) (rank : T → ℕ) (level : ℕ)
    (h : t.RankProgress (fun s => rank (f s)) level) : (t.mapState f).RankProgress rank level := by
  cases t with
  | done x => trivial
  | ask a b hb hab upper lower => exact h

end WordTransition

def serialTransition {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) : SerialState S α T → WordTransition (SerialState S α T) β
  | .source s => match m.step s with
      | .done a => ((next a).step (start a)).mapState (.continuation a)
      | .ask a b hb hab upper lower => .ask a b hb hab (.source upper) (.source lower)
  | .continuation a s => ((next a).step s).mapState (.continuation a)

def serialRank {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (C : ℕ) : SerialState S α T → ℕ
  | .source s => m.rank s + C
  | .continuation a s => (next a).rank s

def WordStateMachine.serial {S α β : Type*} {T : α → Type*} (m : WordStateMachine S α)
    (next : ∀ a, WordStateMachine (T a) β) (start : ∀ a, T a) (C : ℕ)
    (hC : ∀ a, (next a).rank (start a) ≤ C) : WordStateMachine (SerialState S α T) β where
  step := serialTransition m next start
  rank := serialRank m next C
  progress := by
    intro cursor
    cases cursor with
    | source s =>
      cases hs : m.step s with
      | done a =>
        have hp := (next a).progress (start a)
        have hc := hC a
        unfold serialTransition
        dsimp only
        rw [hs]
        apply WordTransition.mapState_progress
        cases ht : (next a).step (start a) with
        | done x => trivial
        | ask u d hd hud upper lower =>
          rw [ht] at hp
          change (next a).rank upper < m.rank s + C ∧ (next a).rank lower < m.rank s + C
          omega
      | ask a b hb hab upper lower =>
        have hp := m.progress s
        rw [hs] at hp
        unfold serialTransition
        dsimp only
        rw [hs]
        change m.rank upper + C < m.rank s + C ∧ m.rank lower + C < m.rank s + C
        omega
    | continuation a s =>
      apply WordTransition.mapState_progress
      exact (next a).progress s

end Blotto
