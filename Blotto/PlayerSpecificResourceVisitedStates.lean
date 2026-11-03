import Blotto.PlayerSpecificFiniteResourceExecution

/-! Proof-only certificates for every actually reachable resource state,
including intermediate prefixes and stopped requests. Runtime execution
still follows one path and never constructs this branch certificate. -/
namespace Blotto.PlayerSpecificResourceVisitedStates
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceRequest
set_option autoImplicit false
set_option maxHeartbeats 2500000

def All {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (P : State N → Prop) : ℕ → State N → Prop
  | 0,s => P s
  | fuel+1,s => P s ∧ match request model p s with
      | none => True
      | some f => ∀ upper : Bool,All model p P fuel (advance model p s f upper)

theorem head {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (P : State N → Prop) (fuel : ℕ) (s : State N) (h : All model p P fuel s) : P s := by
  cases fuel
  · exact h
  · exact h.1

theorem next {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (P : State N → Prop) (fuel : ℕ) (s : State N) (h : All model p P (fuel+1) s)
    (f : Frame N) (hf : request model p s=some f) (upper : Bool) :
    All model p P fuel (advance model p s f upper) := by
  have ht:=h.2
  rw [hf] at ht
  exact ht upper

theorem of_paths {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (P : State N → Prop) (fuel : ℕ) (s : State N)
    (hpaths : ∀ k≤fuel,∀ choices : List Bool,P (PlayerSpecificAlgebraicResourceLoop.run model p k s choices).1) :
    All model p P fuel s := by
  induction fuel generalizing s with
  | zero => exact hpaths 0 (Nat.le_refl _) []
  | succ fuel ih =>
    refine ⟨hpaths 0 (by omega) [],?_⟩
    cases hr : request model p s with
    | none => trivial
    | some f =>
      intro upper
      apply ih
      intro k hk choices
      have hp:=hpaths (k+1) (by omega) (upper::choices)
      simpa only [PlayerSpecificAlgebraicResourceLoop.run,hr,List.headD_cons,List.tail_cons] using hp

theorem output {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (P : State N → Prop) (H fuel : ℕ) (s : State N) (h : All model p P fuel s) (blocks : List (Fin H → Bool)) :
    P (PlayerSpecificFiniteResourceLoop.run model p H fuel s blocks).1 := by
  induction fuel generalizing s blocks with
  | zero => exact h
  | succ fuel ih =>
    cases hr : request model p s with
    | none => simpa only [PlayerSpecificFiniteResourceLoop.run,hr] using h.1
    | some f =>
      let upper:=PlayerSpecificAlgebraicMidpointCoin.run model p.parameters.root f.pair.probability H (blocks.headD (fun _ => false))
      have ht:=next model p P fuel s h f hr upper
      simpa only [PlayerSpecificFiniteResourceLoop.run,hr] using ih (advance model p s f upper) ht blocks.tail

theorem measured_output {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (P : State N → Prop) (H fuel : ℕ) (s : State N) (h : All model p P fuel s) (blocks : List (Fin H → Bool)) :
    P (PlayerSpecificFiniteResourceExecution.run model p H fuel s blocks).1.1 := by
  rw [PlayerSpecificFiniteResourceExecution.value]
  exact output model p P H fuel s h blocks

end Blotto.PlayerSpecificResourceVisitedStates
