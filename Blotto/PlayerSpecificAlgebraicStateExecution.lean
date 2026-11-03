import Blotto.PlayerSpecificAlgebraicActiveListCost
import Blotto.PlayerSpecificAlgebraicResourceState

/-! Measured construction and selected writes of the actual resource
state. Complete consumed/returned arrays and index/list caller work are
priced conservatively, including native copy-on-write array copies. -/
namespace Blotto.PlayerSpecificAlgebraicStateExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

def lengths {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) : FixedArrayTable N Data :=
  FixedArrayTable.ofFn (fun j => (p.rows.read j).length)

def frame {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) (ids : List (Fin N)) : Trace :=
  PlayerSpecificAlgebraicCallerFrame.run
    ([p.parameters.root.polynomial,[p.parameters.root.interval.lo,p.parameters.root.interval.hi]]++
      List.ofFn (fun j => (p.rows.read j).length)++List.ofFn s.data.read)
    ([N,s.active.length,ids.length]++List.range N++List.range N++s.active.map Fin.val++ids.map Fin.val)

def start {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (player : Bool) : State N×ℕ :=
  let data:=FixedArrayTable.ofFn (PlayerSpecificInitialLineageBound.means p player)
  let filtered:=PlayerSpecificAlgebraicActiveListExecution.run model p.parameters.root (lengths p) data (List.finRange N)
  let result:State N:=⟨data,filtered.1⟩
  (result,filtered.2+price model (frame p result (List.finRange N)))

theorem start_value {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (player : Bool) :
    (start model p player).1=PlayerSpecificAlgebraicResourceState.start model p player := by
  simp only [start,PlayerSpecificAlgebraicActiveListExecution.value,lengths,FixedArrayTable.read_ofFn,
    PlayerSpecificAlgebraicResourceState.start]

def update {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N)
    (i j : Fin N) (tail : List (Fin N)) (a b : Data) : State N×ℕ :=
  let data:=(s.data.write i a).write j b
  let filtered:=PlayerSpecificAlgebraicActiveListExecution.run model p.parameters.root (lengths p) data [i,j]
  let result:State N:=⟨data,filtered.1++tail⟩
  (result,filtered.2+price model (frame p s tail)+price model (frame p result [i,j]))

theorem update_value {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N)
    (i j : Fin N) (tail : List (Fin N)) (a b : Data) :
    (update model p s i j tail a b).1=PlayerSpecificAlgebraicResourceState.update model p s i j tail a b := by
  simp only [update,PlayerSpecificAlgebraicActiveListExecution.value,lengths,FixedArrayTable.read_ofFn,
    PlayerSpecificAlgebraicResourceState.update]

end Blotto.PlayerSpecificAlgebraicStateExecution
