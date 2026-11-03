import Blotto.PlayerSpecificAlgebraicEqualityCost

/-! Measured selection of saturated original coordinates. Each exact
field equality is computed once; retained indices and caller words are copied. -/
namespace Blotto.PlayerSpecificUniformItemsExecution
open PlayerSpecificRationalTrace PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frame {N : ℕ} (j : Fin N) (ids result : List (Fin N)) : Trace :=
  PlayerSpecificAlgebraicCallerFrame.run [] ([N,j.val,ids.length,result.length,1]++ids.map Fin.val++result.map Fin.val)

def run {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) :
    List (Fin N) → List (Fin N)×ℕ
  | [] => ([],price model (PlayerSpecificAlgebraicCallerFrame.run [] [N,0,1]))
  | j::ids =>
      let tested:=PlayerSpecificAlgebraicEqualityExecution.run model p.parameters.root.polynomial (s.data.read j) (p.rows.read j).length
      let tail:=run model p s ids
      let result:=if tested.1 then j::tail.1 else tail.1
      (result,tested.2+tail.2+price model (frame j (j::ids) result))

theorem value {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N)
    (ids : List (Fin N)) : (run model p s ids).1=ids.filter
      (fun j => PlayerSpecificAlgebraicField.equal p.parameters.root.polynomial (s.data.read j) (p.rows.read j).length) := by
  induction ids with
  | nil => rfl
  | cons j ids ih => simp only [run,PlayerSpecificAlgebraicEqualityExecution.value,ih,List.filter_cons]

theorem uniform_items {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) :
    (run model p s (List.finRange N)).1=PlayerSpecificAlgebraicGrouping.uniformItems p s := value model p s _

theorem length {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N)
    (ids : List (Fin N)) : (run model p s ids).1.length ≤ ids.length := by
  rw [value]
  exact List.length_filter_le _ _

end Blotto.PlayerSpecificUniformItemsExecution
