import Blotto.PlayerSpecificAlgebraicGroupingHeights

/-! Complete saved-input, retained-output and list/index source frames
for greedy grouping. Every copied group coefficient row is charged. -/
namespace Blotto.PlayerSpecificAlgebraicGroupingFrameCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicGrouping
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem cost {N : ℕ} (model : RationalCostModel) (root : Candidate) (B : ℚ)
    (current : List (Fin N)) (s combined : Data) (rest : List (Fin N)) (result : List (Group N)) (S : ℕ)
    (hm : HasHeight root.polynomial S) (hml : root.polynomial.length≤4)
    (he : HasHeight [root.interval.lo,root.interval.hi,B] S)
    (hs : HasHeight s S) (hsl : s.length≤3) (hc : HasHeight combined S) (hcl : combined.length≤3)
    (hr : ∀ g∈result,HasHeight g.total S ∧ g.total.length≤3)
    (hi : current.length+rest.length≤N) (hg : result.length≤N+1)
    (hp : (result.map Group.members).flatten.length≤N) (hN : N+1≤S) :
    price model (PlayerSpecificAlgebraicGroupingExecution.frame root B current s combined rest result)≤
      500*(N+1)*model.rat (PlayerSpecificAlgebraicComparisonExecution.width S) := by
  let rows:=[root.polynomial,[root.interval.lo,root.interval.hi,B],s,combined]++result.map Group.total
  let words:=[N,current.length,rest.length,result.length,1]++current.map Fin.val++rest.map Fin.val++result.flatMap (fun g => g.members.map Fin.val)
  let W:=PlayerSpecificAlgebraicComparisonExecution.width S
  have hrows : ∀ row∈rows,HasHeight row S ∧ row.length≤21 := by
    intro row hrow
    simp only [rows,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hrow
    rcases hrow with (hrow|hrow|hrow|hrow)|hrow
    · rw [hrow]; exact ⟨hm,by omega⟩
    · rw [hrow]; exact ⟨he,by simp⟩
    · rw [hrow]; exact ⟨hs,by omega⟩
    · rw [hrow]; exact ⟨hc,by omega⟩
    · obtain ⟨g,hg',rfl⟩:=List.mem_map.mp hrow
      exact ⟨(hr g hg').1,(hr g hg').2.trans (by decide)⟩
  have hwords : ∀ word∈words,binaryWordWidth word≤W := by
    intro word hw
    have hwS : word≤S := by
      simp only [words,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with (((hw|hw|hw|hw|hw)|hw)|hw)|hw
      · omega
      · omega
      · omega
      · omega
      · omega
      · obtain ⟨k,_,rfl⟩:=List.mem_map.mp hw; have hk:=k.isLt; omega
      · obtain ⟨k,_,rfl⟩:=List.mem_map.mp hw; have hk:=k.isLt; omega
      · obtain ⟨g,_,hw⟩:=List.mem_flatMap.mp hw
        obtain ⟨k,_,rfl⟩:=List.mem_map.mp hw; have hk:=k.isLt; omega
    exact (control_width word).trans ((Nat.add_le_add_right hwS 1).trans (PlayerSpecificAlgebraicActiveListCost.width_large S).2.2)
  have hflat : (result.flatMap (fun g => g.members.map Fin.val)).length=(result.map Group.members).flatten.length := by
    simp only [List.length_flatMap,List.length_map,List.length_flatten,List.map_map,Function.comp_def]
  have hframe:=PlayerSpecificAlgebraicCallerFrame.cost model rows words S W
    (fun row hrow => (hrows row hrow).1) (fun row hrow => (hrows row hrow).2) hwords
    (PlayerSpecificAlgebraicActiveListCost.width_large S).2.1 (PlayerSpecificAlgebraicActiveListCost.width_large S).1
  apply hframe.trans
  apply Nat.mul_le_mul_right (model.rat W)
  simp only [rows,words,List.length_append,List.length_cons,List.length_nil,List.length_map,hflat]
  omega

end Blotto.PlayerSpecificAlgebraicGroupingFrameCost
