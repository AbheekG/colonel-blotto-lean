import Blotto.PlayerSpecificAlgebraicActiveCost

/-! Complete coefficient-row copies and finite integer caller words.
These reusable frames price actual saved/returned rows and loop indices. -/
namespace Blotto.PlayerSpecificAlgebraicCallerFrame
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run (rows : List Data) (words : List ℕ) : Trace :=
  rows.flatMap copyRow++words.map Event.control

theorem rows_cost (model : RationalCostModel) (rows : List Data) (H W : ℕ)
    (hh : ∀ row∈rows,HasHeight row H) (hl : ∀ row∈rows,row.length≤21)
    (hHW : 1+2*H≤W) (hW : 32≤W) :
    price model (rows.flatMap copyRow)≤66*rows.length*model.rat W := by
  induction rows with
  | nil => simp only [List.flatMap_nil,price,List.map_nil,List.sum_nil,List.length_nil,Nat.mul_zero,Nat.zero_mul,Nat.le_refl]
  | cons row rows ih =>
    have hrow:=PlayerSpecificExtendedCopyCost.row_cost model row H W (hh row List.mem_cons_self)
      (hl row List.mem_cons_self) hHW hW
    have htail:=ih (fun r hr => hh r (List.mem_cons_of_mem row hr)) (fun r hr => hl r (List.mem_cons_of_mem row hr))
    simp only [List.flatMap_cons,price_append,List.length_cons]
    nlinarith only [hrow,htail]

theorem controls_cost (model : RationalCostModel) (words : List ℕ) (W : ℕ)
    (hw : ∀ word∈words,binaryWordWidth word≤W) (hW : 1≤W) :
    price model (words.map Event.control)≤3*words.length*model.rat W := by
  have hf : Fits W (words.map Event.control) := by
    intro e he
    obtain ⟨word,hword,rfl⟩:=List.mem_map.mp he
    exact hw word hword
  simpa only [List.length_map] using price_bound model W hW _ hf

theorem cost (model : RationalCostModel) (rows : List Data) (words : List ℕ) (H W : ℕ)
    (hh : ∀ row∈rows,HasHeight row H) (hl : ∀ row∈rows,row.length≤21)
    (hw : ∀ word∈words,binaryWordWidth word≤W) (hHW : 1+2*H≤W) (hW : 32≤W) :
    price model (run rows words)≤(66*rows.length+3*words.length)*model.rat W := by
  have hr:=rows_cost model rows H W hh hl hHW hW
  have hc:=controls_cost model words W hw (by omega)
  rw [run,price_append]
  nlinarith only [hr,hc]

end Blotto.PlayerSpecificAlgebraicCallerFrame
