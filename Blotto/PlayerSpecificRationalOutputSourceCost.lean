import Blotto.PlayerSpecificOutputFloorRoundSourceCost

/-! Every original output coordinate is rounded once. The source bound
also charges the complete input/output arrays and their indices. -/
namespace Blotto.PlayerSpecificRationalOutputSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights
open PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frameHeight (N T P : ℕ) : ℕ :=
  max (PlayerSpecificOutputFloorPredicateSourceCost.height T P) N+6
def width (N T P : ℕ) : ℕ :=
  PlayerSpecificAlgebraicComparisonExecution.width (frameHeight N T P)
def work (N T P : ℕ) : ℕ :=
  N*PlayerSpecificOutputFloorRoundSourceCost.work T P+
    (141+138*N)*RationalCostModel.schoolbook.rat (width N T P)

theorem cost {N : ℕ} (root : Candidate) (y : FixedArrayTable N Data) (T P : ℕ)
    (hm : PlayerSpecificPolynomialNormalization.Normalized root.polynomial)
    (hm0 : root.polynomial≠[])
    (hml : root.polynomial.length≤4)
    (hv : root.interval.lo<root.interval.hi)
    (hroot : HasHeight root.polynomial T)
    (hends : HasHeight [root.interval.lo,root.interval.hi] T)
    (hy : ∀ j : Fin N,PlayerSpecificAlgebraicReduction.Reduced root.polynomial (y.read j) ∧
      HasHeight (y.read j) T) :
    (PlayerSpecificRationalOutputExecution.run root y P).2≤work N T P := by
  let model:=RationalCostModel.schoolbook
  let measured:=FixedArrayTable.ofFn (fun j : Fin N =>
    PlayerSpecificOutputFloorExecution.round root (y.read j) P)
  let result:=FixedArrayTable.ofFn (fun j : Fin N => (measured.read j).1)
  let S:=frameHeight N T P
  let W:=width N T P
  let R:=model.rat W
  let M:=PlayerSpecificOutputFloorRoundSourceCost.work T P
  have hsum : (∑ j : Fin N,(measured.read j).2)≤N*M := by
    have h:=Finset.sum_le_sum (fun j (_ : j∈Finset.univ) =>
      PlayerSpecificOutputFloorRoundSourceCost.cost root (y.read j) T P
        hm hm0 hml hv hroot hends (hy j))
    simpa only [measured,FixedArrayTable.read_ofFn,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,M] using h
  have hbase : PlayerSpecificOutputFloorPredicateSourceCost.height T P≤S := by
    dsimp only [S,frameHeight]
    exact (le_max_left _ _).trans (Nat.le_add_right _ _)
  have hN : N≤S := by
    dsimp only [S,frameHeight]
    exact (le_max_right _ _).trans (Nat.le_add_right _ _)
  have hT : T≤S := by
    have hc:=PlayerSpecificAlgebraicHeightEnvelope.large
      (PlayerSpecificOutputFloorPredicateSourceCost.inputHeight T P)
    change PlayerSpecificOutputFloorPredicateSourceCost.inputHeight T P+1≤
      PlayerSpecificOutputFloorPredicateSourceCost.height T P at hc
    have ht : T≤PlayerSpecificOutputFloorPredicateSourceCost.inputHeight T P := by
      dsimp only [PlayerSpecificOutputFloorPredicateSourceCost.inputHeight]
      omega
    exact ht.trans ((Nat.le_succ _).trans (hc.trans hbase))
  have hP : P+3≤S := by
    have hc:=PlayerSpecificAlgebraicHeightEnvelope.large
      (PlayerSpecificOutputFloorPredicateSourceCost.inputHeight T P)
    change PlayerSpecificOutputFloorPredicateSourceCost.inputHeight T P+1≤
      PlayerSpecificOutputFloorPredicateSourceCost.height T P at hc
    have hp : P+2≤PlayerSpecificOutputFloorPredicateSourceCost.inputHeight T P := by
      dsimp only [PlayerSpecificOutputFloorPredicateSourceCost.inputHeight]
      omega
    omega
  have hWL:=PlayerSpecificAlgebraicActiveListCost.width_large S
  have hWL' : 32≤W ∧ 1+2*S≤W := by
    simpa only [W,width,S] using ⟨hWL.1,hWL.2.1⟩
  have hW : 32≤W := hWL'.1
  have hNS : N+1≤W := by omega
  have hPS : P+4≤W := by omega
  have hheight : ∀ row∈([root.polynomial,[root.interval.lo,root.interval.hi]]++
      List.ofFn y.read++List.ofFn (fun j : Fin N => [result.read j])),HasHeight row S := by
    intro row hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with ((hr|hr)|hr)|hr
    · rw [hr]; exact PlayerSpecificPolynomialHeights.mono hroot hT
    · rw [hr]; exact PlayerSpecificPolynomialHeights.mono hends hT
    · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hr
      exact PlayerSpecificPolynomialHeights.mono (hy j).2 hT
    · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hr
      have hh:=PlayerSpecificOutputFloorRoundSourceCost.rational_height root (y.read j) P
      have he : result.read j=(PlayerSpecificOutputFloorExecution.round root (y.read j) P).1 := by
        simp only [result,measured,FixedArrayTable.read_ofFn]
      rw [he]
      exact PlayerSpecificPolynomialHeights.cons_height (hh.mono hP)
        (PlayerSpecificPolynomialHeights.nil_height _)
  have hlength : ∀ row∈([root.polynomial,[root.interval.lo,root.interval.hi]]++
      List.ofFn y.read++List.ofFn (fun j : Fin N => [result.read j])),row.length≤21 := by
    intro row hr
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with ((hr|hr)|hr)|hr
    · rw [hr]; omega
    · rw [hr]; simp
    · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hr
      have hl:=(hy j).1.2
      omega
    · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hr
      simp
  have hwords : ∀ word∈([N,P,1]++List.range N++List.range N),binaryWordWidth word≤W := by
    intro word hw
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with ((hw|hw|hw)|hw)|hw
    · rw [hw]; exact (control_width N).trans hNS
    · rw [hw]; exact (control_width P).trans (by omega)
    · rw [hw]; exact (control_width 1).trans (by omega)
    · exact (control_width word).trans (by have h:=List.mem_range.mp hw; omega)
    · exact (control_width word).trans (by have h:=List.mem_range.mp hw; omega)
  have hframe:=PlayerSpecificAlgebraicCallerFrame.cost model
    ([root.polynomial,[root.interval.lo,root.interval.hi]]++
      List.ofFn y.read++List.ofFn (fun j : Fin N => [result.read j]))
    ([N,P,1]++List.range N++List.range N) S W
    hheight hlength hwords (by dsimp only [W,width]; exact hWL.2.1) hW
  have hframe' : price model (PlayerSpecificRationalOutputExecution.frame root y result P)≤
      (141+138*N)*R := by
    change price model (PlayerSpecificAlgebraicCallerFrame.run
      ([root.polynomial,[root.interval.lo,root.interval.hi]]++
        List.ofFn y.read++List.ofFn (fun j : Fin N => [result.read j]))
      ([N,P,1]++List.range N++List.range N))≤_
    simp only [List.length_append,List.length_ofFn,List.length_range,
      List.length_cons,List.length_nil,Nat.reduceAdd] at hframe
    have hs : (66*(2+N+N)+3*(3+N+N))*R=(141+138*N)*R := by ring
    exact hframe.trans_eq hs
  change (∑ j : Fin N,(measured.read j).2)+
    price model (PlayerSpecificRationalOutputExecution.frame root y result P)≤_
  have hsum':=Nat.add_le_add hsum hframe'
  change (∑ j : Fin N,(measured.read j).2)+
    price model (PlayerSpecificRationalOutputExecution.frame root y result P)≤
    N*M+(141+138*N)*R
  exact hsum'

end Blotto.PlayerSpecificRationalOutputSourceCost
