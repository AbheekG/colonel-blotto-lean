import Blotto.PlayerSpecificExpressionVectorExecution

/-! Full finite local-program input/output array, index and return
frames, with size linear in the input and returned row counts. -/
namespace Blotto.PlayerSpecificExpressionVectorFrameCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem cost {k m : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data)
    (result : FixedArrayTable m Data) (S : ℕ) (hm : HasHeight root.polynomial S) (hml : root.polynomial.length≤4)
    (he : HasHeight [root.interval.lo,root.interval.hi] S)
    (hEnv : ∀ j,HasHeight (env.read j) S ∧ (env.read j).length≤3)
    (hResult : ∀ j,HasHeight (result.read j) S ∧ (result.read j).length≤3)
    (hk : k≤S) (hmS : m≤S) (hS : 1≤S) :
    price model (PlayerSpecificExpressionVectorExecution.frame root env result)≤
      200*(k+m+1)*model.rat (PlayerSpecificAlgebraicComparisonExecution.width S) := by
  let rows:=[root.polynomial,[root.interval.lo,root.interval.hi]]++List.ofFn env.read++List.ofFn result.read
  let words:=[k,m,1]++List.range k++List.range m++List.range m
  let W:=PlayerSpecificAlgebraicComparisonExecution.width S
  have hr : ∀ row∈rows,HasHeight row S ∧ row.length≤21 := by
    intro row hrow
    simp only [rows,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hrow
    rcases hrow with ((hrow|hrow)|hrow)|hrow
    · rw [hrow]; exact ⟨hm,by omega⟩
    · rw [hrow]; exact ⟨he,by simp⟩
    · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hrow
      exact ⟨(hEnv j).1,(hEnv j).2.trans (by decide)⟩
    · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hrow
      exact ⟨(hResult j).1,(hResult j).2.trans (by decide)⟩
  have hw : ∀ word∈words,binaryWordWidth word≤W := by
    intro word hword
    have hsmall : word≤S := by
      simp only [words,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range] at hword
      omega
    exact (control_width word).trans ((Nat.add_le_add_right hsmall 1).trans (PlayerSpecificAlgebraicActiveListCost.width_large S).2.2)
  have hc:=PlayerSpecificAlgebraicCallerFrame.cost model rows words S W
    (fun row hrow => (hr row hrow).1) (fun row hrow => (hr row hrow).2) hw
    (PlayerSpecificAlgebraicActiveListCost.width_large S).2.1 (PlayerSpecificAlgebraicActiveListCost.width_large S).1
  apply hc.trans
  apply Nat.mul_le_mul_right (model.rat W)
  simp only [rows,words,List.length_append,List.length_cons,List.length_nil,List.length_ofFn,List.length_range]
  omega

end Blotto.PlayerSpecificExpressionVectorFrameCost
