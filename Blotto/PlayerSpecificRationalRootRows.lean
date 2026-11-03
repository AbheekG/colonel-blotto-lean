import Blotto.PlayerSpecificRationalRootHeight

/-! Actual reconstruction/filter traversal of stored leaves. Each output
list, option branch and enclosing row is copied and priced. -/
namespace Blotto.PlayerSpecificRationalRootRows
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 3000000

def run (model : RationalCostModel) (p : Data) (cache : PlayerSpecificReconstructionCache.Result) : List Interval → Data×ℕ
  | [] => ([],16*cache.word)
  | node::nodes =>
    let head:=PlayerSpecificReconstructionLeafExecution.run model p cache node
    let tail:=run model p cache nodes
    let result:=match head.1 with | none => tail.1 | some q => q::tail.1
    (result,head.2+tail.2+price model (copyRow result)+32*cache.word)

theorem value (model : RationalCostModel) (p : Data) (nodes : List Interval) :
    (run model p (PlayerSpecificReconstructionCache.run model p).1 nodes).1=nodes.filterMap (PlayerSpecificRationalRoots.reconstruct p) := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih =>
    rw [run]
    simp only [PlayerSpecificReconstructionLeafExecution.value,ih,List.filterMap_cons]
    cases PlayerSpecificRationalRoots.reconstruct p node <;> rfl

theorem length (model : RationalCostModel) (p : Data) (cache : PlayerSpecificReconstructionCache.Result) (nodes : List Interval) :
    (run model p cache nodes).1.length≤nodes.length := by
  induction nodes with
  | nil => exact Nat.le_refl 0
  | cons node nodes ih =>
    rw [run]
    dsimp only
    cases (PlayerSpecificReconstructionLeafExecution.run model p cache node).1 <;> simp only [List.length_cons] <;> omega

theorem root (model : RationalCostModel) (p : Data) (nodes : List Interval) (q : ℚ)
    (hq : q∈(run model p (PlayerSpecificReconstructionCache.run model p).1 nodes).1) : evaluate p q=0 := by
  rw [value] at hq
  obtain ⟨node,_,hs⟩:=List.mem_filterMap.mp hq
  exact (PlayerSpecificRationalReconstruction.sound p _ _ _ node q hs).2.2

end Blotto.PlayerSpecificRationalRootRows
