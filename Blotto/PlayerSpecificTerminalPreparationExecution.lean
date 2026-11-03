import Blotto.PlayerSpecificAlgebraicGroupingEntryCost
import Blotto.PlayerSpecificAlgebraicTerminalPreparation

/-! Actual measured terminal preparation: materialize endpoint rows,
filter saturated coordinates once, group once and retain the fractional
head. All source arrays, member lists and returned rows are priced. -/
namespace Blotto.PlayerSpecificTerminalPreparationExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicResourceState
open PlayerSpecificAlgebraicGrouping PlayerSpecificAlgebraicTerminalPreparation
set_option autoImplicit false
set_option maxHeartbeats 2500000

def lengthsFrame {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) : Trace :=
  PlayerSpecificAlgebraicCallerFrame.run (List.ofFn (fun j => (p.rows.read j).length))
    ([N,1]++List.range N++List.range N)

def lengths {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) : FixedArrayTable N Data×ℕ :=
  (FixedArrayTable.ofFn (fun j => (p.rows.read j).length),price model (lengthsFrame p))

def frame {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) (B : ℚ) (result : Prepared N) : Trace :=
  PlayerSpecificAlgebraicCallerFrame.run
    ([p.parameters.root.polynomial,[p.parameters.root.interval.lo,p.parameters.root.interval.hi,B]]++
      List.ofFn s.data.read++result.groups.map Group.total)
    ([N,s.active.length,result.groups.length,1]++List.range N++s.active.map Fin.val++
      result.groups.flatMap (fun g => g.members.map Fin.val)++result.fractional.toList.map Fin.val)

def run {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) (B : ℚ) : Prepared N×ℕ :=
  let cached:=lengths model p
  let items:=PlayerSpecificUniformItemsExecution.run model p s (List.finRange N)
  let grouped:=PlayerSpecificAlgebraicGroupingExecution.run model p.parameters.root cached.1 B items.1
  let result:Prepared N:=⟨grouped.1,s.active.head?⟩
  (result,cached.2+items.2+grouped.2+price model (frame p s B result))

theorem value {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) (B : ℚ) :
    (run model p s B).1=PlayerSpecificAlgebraicTerminalPreparation.prepare model p s B := by
  have he : (FixedArrayTable.ofFn (fun j => (p.rows.read j).length)).read=(fun j => (p.rows.read j).length) := by
    funext j
    exact FixedArrayTable.read_ofFn _ j
  simp only [run,lengths,PlayerSpecificUniformItemsExecution.uniform_items,
    PlayerSpecificAlgebraicGroupingExecution.value,he,PlayerSpecificAlgebraicTerminalPreparation.prepare]

theorem groups_partition {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) (B : ℚ) :
    (((run model p s B).1.groups).map Group.members).flatten=PlayerSpecificAlgebraicGrouping.uniformItems p s ∧
    (run model p s B).1.groups.length≤N := by
  have h:=PlayerSpecificAlgebraicGroupingShape.run model p.parameters.root (lengths model p).1 B
    (PlayerSpecificUniformItemsExecution.run model p s (List.finRange N)).1
  have hl:=PlayerSpecificUniformItemsExecution.length model p s (List.finRange N)
  refine ⟨?_,h.2.trans ?_⟩
  · exact h.1.trans (PlayerSpecificUniformItemsExecution.uniform_items model p s)
  · simpa only [List.length_finRange] using hl

end Blotto.PlayerSpecificTerminalPreparationExecution
