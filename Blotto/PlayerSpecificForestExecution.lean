import Blotto.PlayerSpecificSplitTraceCost

/-! Actual pruned dyadic traversal with source traces. It returns exactly
the already verified root forest, including zero pruning, split reuse and
retained output-record copies. -/
namespace Blotto.PlayerSpecificForestExecution
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 4000000

def copyForest (rows : List Interval) : Trace :=
  .control rows.length::rows.flatMap PlayerSpecificSplitExecution.copyInterval

def frame (fuel : ℕ) (node : Interval) : Trace :=
  PlayerSpecificSplitExecution.copyInterval node++[.control fuel,.control node.count,.control 1]

def run {p : Data} (prepared : Prepared p) : ℕ → Interval → List Interval×Trace
  | 0,node =>
    let pre := frame 0 node
    if node.count=0 then ([],pre++[.control 0]) else ([node],pre++copyForest [node])
  | fuel+1,node =>
    let pre := frame (fuel+1) node
    if node.count=0 then ([],pre++[.control 0]) else
      let divided := PlayerSpecificSplitExecution.run prepared node
      let left := run prepared fuel divided.1.1
      let right := run prepared fuel divided.1.2
      let result := left.1++right.1
      (result,pre++divided.2++left.2++right.2++copyForest result)

theorem value {p : Data} (prepared : Prepared p) (fuel : ℕ) (node : Interval) :
    (run prepared fuel node).1=PlayerSpecificIsolationForest.run prepared fuel node := by
  induction fuel generalizing node with
  | zero =>
    rw [run,PlayerSpecificIsolationForest.run]
    split <;> rfl
  | succ fuel ih =>
    rw [run,PlayerSpecificIsolationForest.run]
    split
    · rfl
    · simp only [ih,PlayerSpecificSplitExecution.value]

theorem copyForest_length (rows : List Interval) : (copyForest rows).length=5*rows.length+1 := by
  induction rows with
  | nil => rfl
  | cons node rows ih =>
    simp only [copyForest,List.flatMap_cons,List.length_cons,List.length_append,PlayerSpecificSplitExecution.copyInterval_length] at ih ⊢
    omega

theorem frame_length (fuel : ℕ) (node : Interval) : (frame fuel node).length=8 := by
  simp only [frame,List.length_append,PlayerSpecificSplitExecution.copyInterval_length,List.length_cons,List.length_nil]

end Blotto.PlayerSpecificForestExecution
