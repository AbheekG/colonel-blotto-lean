import Blotto.PlayerSpecificAlgebraicCoinCost
import Blotto.PlayerSpecificFiniteResourceLoop

/-! A measured execution of the actual adaptive resource loop. Requests,
coins, selected updates and recursive results are retained once. All
caller state copies, bit-view/index words and return counters are priced. -/
namespace Blotto.PlayerSpecificFiniteResourceExecution
open PlayerSpecificRationalTrace PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frame {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (H fuel blocks visits : ℕ) (s : State N) : ℕ :=
  price model (PlayerSpecificAlgebraicStateExecution.frame p s [])+
    price model (PlayerSpecificAlgebraicCallerFrame.run [] ([H,fuel,blocks,visits,1]++List.range blocks))+blocks

def run {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (H : ℕ) :
    ℕ → State N → List (Fin H → Bool) → (State N×ℕ)×ℕ
  | 0,s,blocks => ((s,0),frame model p H 0 blocks.length 0 s)
  | fuel+1,s,blocks =>
      let request:=PlayerSpecificAlgebraicRequestExecution.request model p s
      match request.1 with
      | none => ((s,0),request.2+frame model p H (fuel+1) blocks.length 0 s)
      | some f =>
          let coin:=PlayerSpecificAlgebraicCoinExecution.run model p.parameters.root f.pair.probability H (blocks.headD (fun _ => false))
          let next:=PlayerSpecificAlgebraicRequestExecution.advance model p s f coin.1
          let tail:=run model p H fuel next.1 blocks.tail
          ((tail.1.1,tail.1.2+1),request.2+coin.2+next.2+tail.2+
            frame model p H (fuel+1) blocks.length (tail.1.2+1) tail.1.1)

theorem value {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (H fuel : ℕ) (s : State N) (blocks : List (Fin H → Bool)) :
    (run model p H fuel s blocks).1=PlayerSpecificFiniteResourceLoop.run model p H fuel s blocks := by
  induction fuel generalizing s blocks with
  | zero => rfl
  | succ fuel ih =>
    simp only [run,PlayerSpecificAlgebraicRequestExecution.request_value,PlayerSpecificFiniteResourceLoop.run]
    cases he : PlayerSpecificAlgebraicResourceRequest.request model p s with
    | none => rfl
    | some f =>
      simp only [PlayerSpecificAlgebraicCoinExecution.value,PlayerSpecificAlgebraicRequestExecution.advance_value,ih]

theorem visits_le {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (H fuel : ℕ) (s : State N) (blocks : List (Fin H → Bool)) :
    (run model p H fuel s blocks).1.2≤fuel := by
  rw [value]
  obtain ⟨choices,hchoices,he⟩:=PlayerSpecificFiniteResourceLoop.path_refinement model p H fuel s blocks
  rw [he]
  clear he hchoices
  induction fuel generalizing s choices with
  | zero => exact Nat.zero_le _
  | succ fuel ih =>
    simp only [PlayerSpecificAlgebraicResourceLoop.run]
    split
    · exact Nat.zero_le _
    · dsimp only
      exact Nat.add_le_add_right (ih _ _) 1

end Blotto.PlayerSpecificFiniteResourceExecution
