import Blotto.WordMachineFallback

/-! Deterministic lower-leaf identities for the retained machine model.
These proof joins preserve zero/one-probability branches: lowerLeaf follows
syntactic lower successors regardless of probability. -/

namespace Blotto
namespace WordChoiceTree

def lowerLeaf {α : Type*} : WordChoiceTree α→α
  | .leaf x=>x
  | .fork _ _ _ _ _ lower=>lower.lowerLeaf

theorem lowerLeaf_map {α β : Type*} (tree : WordChoiceTree α) (f : α→β) :
    (tree.map f).lowerLeaf=f tree.lowerLeaf:=by
  induction tree with
  | leaf _=>rfl
  | fork _ _ _ _ _ _ _ hl=>exact hl

theorem lowerLeaf_bind {α β : Type*} (tree : WordChoiceTree α) (f : α→WordChoiceTree β) :
    (tree.bind f).lowerLeaf=(f tree.lowerLeaf).lowerLeaf:=by
  induction tree with
  | leaf _=>rfl
  | fork _ _ _ _ _ _ _ hl=>exact hl
end WordChoiceTree

namespace WordStateMachine

theorem chooseLeaf_eq_lowerLeaf {S α : Type*} (machine : WordStateMachine S α) (state : S) :
    machine.chooseLeaf state=(machine.specification state).lowerLeaf:=by
  conv_lhs=>unfold chooseLeaf
  conv_rhs=>unfold specification
  cases hs : machine.step state with
  | done _=>rfl
  | ask _ _ _ _ _ lower=>exact chooseLeaf_eq_lowerLeaf machine lower
termination_by machine.rank state
decreasing_by
  have hp:=machine.progress state
  rw [hs] at hp
  exact hp.2

theorem mapped_chooseLeaf {S α β : Type*} (machine : WordStateMachine S α) (f : α→β) (state : S) :
    (machine.mapped f).chooseLeaf state=f (machine.chooseLeaf state):=by
  rw [chooseLeaf_eq_lowerLeaf,mapped_specification,WordChoiceTree.lowerLeaf_map,←chooseLeaf_eq_lowerLeaf]

theorem restricted_chooseLeaf {S α : Type*} (machine : WordStateMachine S α) (I : S→Prop) (P : α→Prop)
    (hI : ∀ s,I s→(machine.step s).Postcondition I P) (state : {s // I s}) :
    ((machine.restricted I P hI).chooseLeaf state).1=machine.chooseLeaf state.1:=by
  rw [chooseLeaf_eq_lowerLeaf]
  rw [←WordChoiceTree.lowerLeaf_map ((machine.restricted I P hI).specification state) Subtype.val,
    restricted_specification,←chooseLeaf_eq_lowerLeaf]

theorem serial_chooseLeaf {S α β : Type*} {T : α→Type*} (machine : WordStateMachine S α)
    (next : ∀ a,WordStateMachine (T a) β) (start : ∀ a,T a) (C : ℕ)
    (hC : ∀ a,(next a).rank (start a)≤C) (state : S) :
    (machine.serial next start C hC).chooseLeaf (.source state)=
      (next (machine.chooseLeaf state)).chooseLeaf (start (machine.chooseLeaf state)):=by
  rw [chooseLeaf_eq_lowerLeaf,serial_source_specification,WordChoiceTree.lowerLeaf_bind,
    ←chooseLeaf_eq_lowerLeaf,←chooseLeaf_eq_lowerLeaf]

end WordStateMachine
end Blotto
