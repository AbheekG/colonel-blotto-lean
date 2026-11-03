import Blotto.PlayerSpecificNestedTerminalPreparationSourceCost

/-! Restoration uses a cached finite focus, never an opaque permutation
callback. Each fixed swap index and returned coefficient row is retained. -/
namespace Blotto.PlayerSpecificNestedRestoreExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def packing (focus : Fin 3) : Trace :=
  (focus.val::List.ofFn (fun j : Fin 3 => ((Equiv.swap focus 2) j).val)).map Event.control++List.replicate 6 (.control 1)
def run (model : RationalCostModel) (root : Candidate) (focus : Fin 3) (a : FixedArrayTable 3 Data) : FixedArrayTable 3 Data×ℕ :=
  let indexed:=FixedArrayTable.ofFn (fun j : Fin 3 => let index:=(Equiv.swap focus 2) j; (index,a.read index))
  let result:=FixedArrayTable.ofFn (fun j => (indexed.read j).2)
  (result,price model (PlayerSpecificExpressionVectorExecution.frame root a result)+price model (packing focus))

theorem value (model : RationalCostModel) (root : Candidate) (focus : Fin 3) (a : FixedArrayTable 3 Data) :
    (run model root focus a).1=PlayerSpecificAlgebraicNestedTerminalDraw.restore (Equiv.swap focus 2) a := by
  simp only [run,FixedArrayTable.read_ofFn,PlayerSpecificAlgebraicNestedTerminalDraw.restore]
theorem packing_cost (model : RationalCostModel) (focus : Fin 3) : price model (packing focus)≤28 := by
  fin_cases focus <;> simp only [packing,price,List.map_append,Function.comp_def,List.map_ofFn,List.map_cons,
    List.sum_append,List.sum_cons,List.map_replicate,List.sum_replicate,List.sum_ofFn,Event.price] <;> decide
theorem price_equation (model : RationalCostModel) (root : Candidate) (focus : Fin 3) (a : FixedArrayTable 3 Data) :
    (run model root focus a).2=price model (PlayerSpecificExpressionVectorExecution.frame root a (run model root focus a).1)+price model (packing focus) := by
  simp only [run]

end Blotto.PlayerSpecificNestedRestoreExecution
