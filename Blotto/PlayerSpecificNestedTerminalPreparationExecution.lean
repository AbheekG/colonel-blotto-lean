import Blotto.PlayerSpecificNestedTerminalEndpointSourceCost

/-! Terminal preparation retains its finite focus directly, avoiding
an opaque runtime permutation callback. Its native view is the checked
original input/permutation record. Every field/backend return is priced. -/
namespace Blotto.PlayerSpecificNestedTerminalPreparationExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicNestedTerminalInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Prepared where
  input : PlayerSpecificAlgebraicNestedInput.Input
  focus : Fin 3

def native (p : Prepared) : PlayerSpecificAlgebraicNestedTerminalInput.Prepared := ⟨p.input,Equiv.swap p.focus 2⟩
def fields (a : Input) : FixedArrayTable 13 Data := FixedArrayTable.ofFn
  ![a.budget,a.long.read 0,a.long.read 1,a.long.read 2,a.short.read 0,a.short.read 1,a.short.read 2,
    a.capacity.read 0,a.capacity.read 1,a.capacity.read 2,a.resource.read 0,a.resource.read 1,a.resource.read 2]
def frame (root : Candidate) (a : Input) (p : Prepared) : Trace :=
  PlayerSpecificExpressionVectorExecution.frame root (fields a) (PlayerSpecificAlgebraicNestedInput.environment p.input [])
def packing (f : Fin 3) : Trace :=
  [.control f.val,.control ((Equiv.swap f 2) 0).val,.control ((Equiv.swap f 2) 1).val,.control ((Equiv.swap f 2) 2).val]++
    List.replicate 12 (.control 1)

def run (model : RationalCostModel) (root : Candidate) (a : Input) : Prepared×ℕ :=
  let focus:=PlayerSpecificNestedFocusExecution.run model root a
  let permutation:=Equiv.swap focus.1 2
  let first:=PlayerSpecificNestedTerminalEndpointExecution.run model root a (permutation 0)
  let second:=PlayerSpecificNestedTerminalEndpointExecution.run model root a (permutation 1)
  let probability:=PlayerSpecificFieldDivisionExecution.run model root.polynomial (a.resource.read focus.1) (a.capacity.read focus.1)
  let result:Prepared:=⟨⟨a.budget,first.1,second.1,a.long.read focus.1,a.short.read focus.1,probability.1⟩,focus.1⟩
  (result,focus.2+first.2+second.2+probability.2+price model (frame root a result)+price model (packing focus.1))

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) :
    native (run model root a).1=PlayerSpecificAlgebraicNestedTerminalInput.prepare model root a := by
  simp only [run,native,PlayerSpecificNestedFocusExecution.value,PlayerSpecificNestedTerminalEndpointExecution.value,
    PlayerSpecificFieldDivisionExecution.value,PlayerSpecificAlgebraicNestedTerminalInput.prepare]
theorem focus_value (model : RationalCostModel) (root : Candidate) (a : Input) :
    (run model root a).1.focus=PlayerSpecificAlgebraicNestedTerminalInput.focus model root a := by
  simp only [run,PlayerSpecificNestedFocusExecution.value]
theorem input_value (model : RationalCostModel) (root : Candidate) (a : Input) :
    (run model root a).1.input=(PlayerSpecificAlgebraicNestedTerminalInput.prepare model root a).input :=
  congrArg PlayerSpecificAlgebraicNestedTerminalInput.Prepared.input (value model root a)
theorem packing_cost (model : RationalCostModel) (f : Fin 3) : price model (packing f)≤40 := by
  fin_cases f <;> simp only [packing,price,List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,
    List.sum_nil,List.map_replicate,List.sum_replicate,Event.price] <;> decide

theorem price_equation (model : RationalCostModel) (root : Candidate) (a : Input) :
    (run model root a).2=(PlayerSpecificNestedFocusExecution.run model root a).2+
      (PlayerSpecificNestedTerminalEndpointExecution.run model root a ((Equiv.swap (PlayerSpecificAlgebraicNestedTerminalInput.focus model root a) 2) 0)).2+
      (PlayerSpecificNestedTerminalEndpointExecution.run model root a ((Equiv.swap (PlayerSpecificAlgebraicNestedTerminalInput.focus model root a) 2) 1)).2+
      (PlayerSpecificFieldDivisionExecution.run model root.polynomial (a.resource.read (PlayerSpecificAlgebraicNestedTerminalInput.focus model root a))
        (a.capacity.read (PlayerSpecificAlgebraicNestedTerminalInput.focus model root a))).2+
      price model (frame root a (run model root a).1)+price model (packing (PlayerSpecificAlgebraicNestedTerminalInput.focus model root a)) := by
  simp only [run,PlayerSpecificNestedFocusExecution.value]

end Blotto.PlayerSpecificNestedTerminalPreparationExecution
