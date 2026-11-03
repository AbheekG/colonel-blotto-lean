import Blotto.PlayerSpecificAlgebraicMidpointCoin

/-! A finite-bit resource path. Each reached cached pair consumes the
next fixed-size fair-bit block and performs one exact midpoint comparison.
No branch tree or supplied Boolean decision oracle enters this program. -/
namespace Blotto.PlayerSpecificFiniteResourceLoop
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceRequest
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (H : ℕ) :
    ℕ → State N → List (Fin H → Bool) → State N × ℕ
  | 0,s,_ => (s,0)
  | fuel+1,s,blocks =>
      match request model p s with
      | none => (s,0)
      | some f =>
          let choice:=PlayerSpecificAlgebraicMidpointCoin.run model p.parameters.root f.pair.probability H (blocks.headD (fun _ => false))
          let next:=advance model p s f choice
          let result:=run model p H fuel next blocks.tail
          (result.1,result.2+1)

theorem path_refinement {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (H fuel : ℕ) (s : State N) (blocks : List (Fin H → Bool)) :
    ∃ choices : List Bool,choices.length=(run model p H fuel s blocks).2 ∧
      run model p H fuel s blocks=PlayerSpecificAlgebraicResourceLoop.run model p fuel s choices := by
  induction fuel generalizing s blocks with
  | zero => exact ⟨[],rfl,rfl⟩
  | succ fuel ih =>
      cases he : request model p s with
      | none =>
          refine ⟨[],by simp only [run,he,List.length_nil],?_⟩
          simp only [run,he,PlayerSpecificAlgebraicResourceLoop.stop model p (fuel+1) s [] he]
      | some f =>
          let choice:=PlayerSpecificAlgebraicMidpointCoin.run model p.parameters.root f.pair.probability H (blocks.headD (fun _ => false))
          obtain ⟨choices,hlen,heq⟩:=ih (advance model p s f choice) blocks.tail
          refine ⟨choice::choices,?_,?_⟩
          · simpa only [List.length_cons,run,he] using congrArg (fun n : ℕ => n+1) hlen
          · simp only [run,he,PlayerSpecificAlgebraicResourceLoop.run,List.headD_cons,List.tail_cons]
            exact congrArg (fun r : State N × ℕ => (r.1,r.2+1)) heq

def blocks (fuel H : ℕ) (bits : Fin (fuel*H) → Bool) : List (Fin H → Bool) :=
  List.ofFn (fun i : Fin fuel => fun j : Fin H => bits ⟨i.val*H+j.val,by
    have hi:=i.isLt
    have hj:=j.isLt
    have hmul:=Nat.mul_le_mul_right H (show i.val+1≤fuel by omega)
    nlinarith⟩)

theorem blocks_length (fuel H : ℕ) (bits : Fin (fuel*H) → Bool) : (blocks fuel H bits).length=fuel :=
  List.length_ofFn

def draw {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (player : Bool) (H : ℕ)
    (bits : Fin ((N-1)*H) → Bool) : State N × ℕ :=
  run RationalCostModel.schoolbook p H (N-1) (start RationalCostModel.schoolbook p player) (blocks (N-1) H bits)

theorem draw_refinement {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (player : Bool) (H : ℕ)
    (bits : Fin ((N-1)*H) → Bool) :
    ∃ choices : List Bool,choices.length=(draw p player H bits).2 ∧
      draw p player H bits=PlayerSpecificAlgebraicPathContract.drawPath p player choices :=
  path_refinement RationalCostModel.schoolbook p H (N-1) (start RationalCostModel.schoolbook p player) (blocks (N-1) H bits)

end Blotto.PlayerSpecificFiniteResourceLoop
