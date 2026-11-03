import Blotto.PlayerSpecificAlgebraicUpdateCost
import Blotto.PlayerSpecificAlgebraicResourceRequest

/-! Measured request/advance use the actual cached pair and the measured
selected writes. There is one pair execution per reached request. -/
namespace Blotto.PlayerSpecificAlgebraicRequestExecution
open PlayerSpecificRationalTrace PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceRequest
set_option autoImplicit false
set_option maxHeartbeats 2500000

def request {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) : Option (Frame N)×ℕ :=
  match s.active with
  | [] => (none,price model (PlayerSpecificAlgebraicStateExecution.frame p s []))
  | [_] => (none,price model (PlayerSpecificAlgebraicStateExecution.frame p s []))
  | i::j::tail =>
      let pair:=PlayerSpecificAlgebraicPairExecution.run model p.parameters.root
        (p.rows.read i).length (p.rows.read j).length (s.data.read i) (s.data.read j)
      (some ⟨i,j,tail,pair.1⟩,pair.2+price model (PlayerSpecificAlgebraicStateExecution.frame p s tail))

theorem request_value {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) :
    (request model p s).1=PlayerSpecificAlgebraicResourceRequest.request model p s := by
  unfold request PlayerSpecificAlgebraicResourceRequest.request
  split <;> simp_all only [PlayerSpecificAlgebraicPairExecution.value]

def advance {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (f : Frame N) (upper : Bool) : State N×ℕ :=
  PlayerSpecificAlgebraicStateExecution.update model p s f.first f.second f.tail
    (if upper then f.pair.upperA else f.pair.lowerA) (if upper then f.pair.upperB else f.pair.lowerB)

theorem advance_value {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (f : Frame N) (upper : Bool) :
    (advance model p s f upper).1=PlayerSpecificAlgebraicResourceRequest.advance model p s f upper := by
  exact PlayerSpecificAlgebraicStateExecution.update_value model p s f.first f.second f.tail _ _

end Blotto.PlayerSpecificAlgebraicRequestExecution
