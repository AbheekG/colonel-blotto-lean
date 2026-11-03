import Blotto.PlayerSpecificAlgebraicStateExecution

/-! Complete state-array and active-index caller frames have linear
source size. All row/word bounds are derived from their finite contents. -/
namespace Blotto.PlayerSpecificAlgebraicStateFrameCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace PlayerSpecificAlgebraicResourceState
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem cost {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N)
    (s : State N) (ids : List (Fin N)) (S : ℕ) (hN : N≤S) (ha : s.active.length≤S) (hi : ids.length≤S)
    (hm : HasHeight p.parameters.root.polynomial S) (he : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi] S)
    (hml : p.parameters.root.polynomial.length≤4)
    (hl : ∀ j,HasHeight (p.rows.read j).length S) (hr : ∀ j,HasHeight (s.data.read j) S)
    (hll : ∀ j,(p.rows.read j).length.length≤3) (hrl : ∀ j,(s.data.read j).length≤3) :
    price model (PlayerSpecificAlgebraicStateExecution.frame p s ids)≤
      150*(N+s.active.length+ids.length+1)*model.rat (PlayerSpecificAlgebraicComparisonExecution.width S) := by
  let W:=PlayerSpecificAlgebraicComparisonExecution.width S
  let rows:=[p.parameters.root.polynomial,[p.parameters.root.interval.lo,p.parameters.root.interval.hi]]++
    List.ofFn (fun j => (p.rows.read j).length)++List.ofFn s.data.read
  let words:=[N,s.active.length,ids.length]++List.range N++List.range N++s.active.map Fin.val++ids.map Fin.val
  have hh : ∀ row∈rows,HasHeight row S := by
    intro row hrow
    simp only [rows,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hrow
    rcases hrow with ((rfl|rfl)|hrow)|hrow
    · exact hm
    · exact he
    · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hrow
      exact hl j
    · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hrow
      exact hr j
  have hlen : ∀ row∈rows,row.length≤21 := by
    intro row hrow
    simp only [rows,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hrow
    rcases hrow with ((rfl|rfl)|hrow)|hrow
    · omega
    · simp
    · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hrow
      exact (hll j).trans (by decide)
    · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hrow
      exact (hrl j).trans (by decide)
  have hw : ∀ word∈words,binaryWordWidth word≤W := by
    intro word hword
    have hb : word≤S := by
      simp only [words,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hword
      rcases hword with (((hword|hword)|hword)|hword)|hword
      · rcases hword with hw|hw|hw <;> omega
      · exact (Nat.le_of_lt (List.mem_range.mp hword)).trans hN
      · exact (Nat.le_of_lt (List.mem_range.mp hword)).trans hN
      · obtain ⟨j,_,rfl⟩:=List.mem_map.mp hword
        exact (Nat.le_of_lt j.isLt).trans hN
      · obtain ⟨j,_,rfl⟩:=List.mem_map.mp hword
        exact (Nat.le_of_lt j.isLt).trans hN
    exact (control_width word).trans ((Nat.add_le_add_right hb 1).trans (PlayerSpecificAlgebraicActiveListCost.width_large S).2.2)
  have hc:=PlayerSpecificAlgebraicCallerFrame.cost model rows words S W hh hlen hw
    (PlayerSpecificAlgebraicActiveListCost.width_large S).2.1 (PlayerSpecificAlgebraicActiveListCost.width_large S).1
  apply hc.trans
  apply Nat.mul_le_mul_right (model.rat W)
  simp only [rows,words,List.length_append,List.length_ofFn,List.length_range,List.length_map,List.length_cons,List.length_nil]
  omega

end Blotto.PlayerSpecificAlgebraicStateFrameCost
