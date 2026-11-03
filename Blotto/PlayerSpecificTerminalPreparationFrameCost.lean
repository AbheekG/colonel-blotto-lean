import Blotto.PlayerSpecificTerminalPreparationExecution

/-! Complete terminal preparation array/list/return work. The finite
index representation and optional fractional return are explicitly priced. -/
namespace Blotto.PlayerSpecificTerminalPreparationFrameCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicGrouping PlayerSpecificAlgebraicTerminalPreparation
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem lengths {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (S : ℕ)
    (hl : ∀ j,HasHeight (p.rows.read j).length S ∧ (p.rows.read j).length.length≤3) (hN : N+1≤S) :
    price model (PlayerSpecificTerminalPreparationExecution.lengthsFrame p)≤
      100*(N+1)*model.rat (PlayerSpecificAlgebraicComparisonExecution.width S) := by
  let W:=PlayerSpecificAlgebraicComparisonExecution.width S
  have hr : ∀ row∈List.ofFn (fun j => (p.rows.read j).length),HasHeight row S ∧ row.length≤21 := by
    intro row hrow
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hrow
    exact ⟨(hl j).1,(hl j).2.trans (by decide)⟩
  have hw : ∀ word∈[N,1]++List.range N++List.range N,binaryWordWidth word≤W := by
    intro word hword
    have hsmall : word≤S := by
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range] at hword
      omega
    exact (control_width word).trans ((Nat.add_le_add_right hsmall 1).trans (PlayerSpecificAlgebraicActiveListCost.width_large S).2.2)
  have hc:=PlayerSpecificAlgebraicCallerFrame.cost model (List.ofFn (fun j => (p.rows.read j).length)) ([N,1]++List.range N++List.range N) S W
    (fun row hrow => (hr row hrow).1) (fun row hrow => (hr row hrow).2) hw
    (PlayerSpecificAlgebraicActiveListCost.width_large S).2.1 (PlayerSpecificAlgebraicActiveListCost.width_large S).1
  apply hc.trans
  apply Nat.mul_le_mul_right (model.rat W)
  simp only [List.length_ofFn,List.length_append,List.length_cons,List.length_nil,List.length_range]
  omega

theorem frame {N : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N)
    (B : ℚ) (result : Prepared N) (S : ℕ)
    (hm : HasHeight p.parameters.root.polynomial S) (hml : p.parameters.root.polynomial.length≤4)
    (he : HasHeight [p.parameters.root.interval.lo,p.parameters.root.interval.hi,B] S)
    (hs : ∀ j,HasHeight (s.data.read j) S ∧ (s.data.read j).length≤3)
    (hr : ∀ g∈result.groups,HasHeight g.total S ∧ g.total.length≤3)
    (ha : s.active.length≤N) (hg : result.groups.length≤N)
    (hp : (result.groups.map Group.members).flatten.length≤N) (hN : N+1≤S) :
    price model (PlayerSpecificTerminalPreparationExecution.frame p s B result)≤
      500*(N+1)*model.rat (PlayerSpecificAlgebraicComparisonExecution.width S) := by
  let rows:=[p.parameters.root.polynomial,[p.parameters.root.interval.lo,p.parameters.root.interval.hi,B]]++List.ofFn s.data.read++result.groups.map Group.total
  let words:=[N,s.active.length,result.groups.length,1]++List.range N++s.active.map Fin.val++
    result.groups.flatMap (fun g => g.members.map Fin.val)++result.fractional.toList.map Fin.val
  let W:=PlayerSpecificAlgebraicComparisonExecution.width S
  have hrows : ∀ row∈rows,HasHeight row S ∧ row.length≤21 := by
    intro row hrow
    simp only [rows,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hrow
    rcases hrow with ((hrow|hrow)|hrow)|hrow
    · rw [hrow]; exact ⟨hm,by omega⟩
    · rw [hrow]; exact ⟨he,by simp⟩
    · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hrow
      exact ⟨(hs j).1,(hs j).2.trans (by decide)⟩
    · obtain ⟨g,hg',rfl⟩:=List.mem_map.mp hrow
      exact ⟨(hr g hg').1,(hr g hg').2.trans (by decide)⟩
  have hwords : ∀ word∈words,binaryWordWidth word≤W := by
    intro word hw
    have hwS : word≤S := by
      simp only [words,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with ((((hw|hw|hw|hw)|hw)|hw)|hw)|hw
      · omega
      · omega
      · omega
      · omega
      · have h:=List.mem_range.mp hw; omega
      · obtain ⟨k,_,rfl⟩:=List.mem_map.mp hw; have h:=k.isLt; omega
      · obtain ⟨g,_,hw⟩:=List.mem_flatMap.mp hw
        obtain ⟨k,_,rfl⟩:=List.mem_map.mp hw; have h:=k.isLt; omega
      · obtain ⟨k,_,rfl⟩:=List.mem_map.mp hw; have h:=k.isLt; omega
    exact (control_width word).trans ((Nat.add_le_add_right hwS 1).trans (PlayerSpecificAlgebraicActiveListCost.width_large S).2.2)
  have hflat : (result.groups.flatMap (fun g => g.members.map Fin.val)).length=(result.groups.map Group.members).flatten.length := by
    simp only [List.length_flatMap,List.length_map,List.length_flatten,List.map_map,Function.comp_def]
  have ho : result.fractional.toList.length≤1 := Option.length_toList_le
  have hc:=PlayerSpecificAlgebraicCallerFrame.cost model rows words S W
    (fun row hrow => (hrows row hrow).1) (fun row hrow => (hrows row hrow).2) hwords
    (PlayerSpecificAlgebraicActiveListCost.width_large S).2.1 (PlayerSpecificAlgebraicActiveListCost.width_large S).1
  apply hc.trans
  apply Nat.mul_le_mul_right (model.rat W)
  simp only [rows,words,List.length_append,List.length_cons,List.length_nil,List.length_ofFn,List.length_map,List.length_range,hflat]
  omega

end Blotto.PlayerSpecificTerminalPreparationFrameCost
