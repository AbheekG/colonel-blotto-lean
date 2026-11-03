import Blotto.PlayerSpecificDescriptorProgramExecution

/-! Complete segment-table construction/copy/index frames, linear in
the actual input and endpoint-row count. -/
namespace Blotto.PlayerSpecificDescriptorProgramFrameCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem rows_property {n m : ℕ} (d : Descriptor n m) (P : Data → Prop)
    (hw : ∀ slot,P (d.weights.read slot)) (hp : ∀ slot j,P ((d.first.read slot).read j))
    (hq : ∀ slot j,P ((d.second.read slot).read j)) :
    ∀ row∈PlayerSpecificDescriptorProgramExecution.rows d,P row := by
  intro row hrow
  simp only [PlayerSpecificDescriptorProgramExecution.rows,List.mem_append] at hrow
  rcases hrow with (hrow|hrow)|hrow
  · obtain ⟨slot,rfl⟩:=List.mem_ofFn.mp hrow; exact hw slot
  · obtain ⟨entries,hentries,hrow⟩:=List.mem_flatten.mp hrow
    obtain ⟨slot,rfl⟩:=List.mem_ofFn.mp hentries
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hrow; exact hp slot j
  · obtain ⟨entries,hentries,hrow⟩:=List.mem_flatten.mp hrow
    obtain ⟨slot,rfl⟩:=List.mem_ofFn.mp hentries
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hrow; exact hq slot j

theorem rows_length {n m : ℕ} (d : Descriptor n m) :
    (PlayerSpecificDescriptorProgramExecution.rows d).length=m+ m*n+m*n := by
  simp only [PlayerSpecificDescriptorProgramExecution.rows,List.length_append,List.length_ofFn,List.length_flatten,
    List.map_ofFn,Function.comp_def,List.sum_ofFn,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]

theorem cost {k n m : ℕ} (model : RationalCostModel) (root : Candidate) (env : FixedArrayTable k Data)
    (d : Descriptor n m) (S : ℕ) (hm : HasHeight root.polynomial S) (hml : root.polynomial.length≤4)
    (he : HasHeight [root.interval.lo,root.interval.hi] S)
    (hEnv : ∀ j,HasHeight (env.read j) S ∧ (env.read j).length≤3)
    (hRows : ∀ row∈PlayerSpecificDescriptorProgramExecution.rows d,HasHeight row S ∧ row.length≤3)
    (hk : k≤S) (hn : n≤S) (hmS : m≤S) (hS : 1≤S) :
    price model (PlayerSpecificDescriptorProgramExecution.frame root env d)≤
      1000*(k+m*(2*n+1)+1)*model.rat (PlayerSpecificAlgebraicComparisonExecution.width S) := by
  let rows:=[root.polynomial,[root.interval.lo,root.interval.hi]]++List.ofFn env.read++PlayerSpecificDescriptorProgramExecution.rows d
  let words:=[k,n,m,1]++List.range k++List.range m++List.range m++(List.replicate m (List.range n++List.range n)).flatten
  let W:=PlayerSpecificAlgebraicComparisonExecution.width S
  have hr : ∀ row∈rows,HasHeight row S ∧ row.length≤21 := by
    intro row hrow
    simp only [rows,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hrow
    rcases hrow with ((hrow|hrow)|hrow)|hrow
    · rw [hrow]; exact ⟨hm,by omega⟩
    · rw [hrow]; exact ⟨he,by simp⟩
    · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hrow
      exact ⟨(hEnv j).1,(hEnv j).2.trans (by decide)⟩
    · exact ⟨(hRows row hrow).1,(hRows row hrow).2.trans (by decide)⟩
  have hw : ∀ word∈words,binaryWordWidth word≤W := by
    intro word hword
    have hsmall : word≤S := by
      simp only [words,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range] at hword
      rcases hword with ((((hword|hword|hword|hword)|hword)|hword)|hword)|hword
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · obtain ⟨entries,hentries,hword⟩:=List.mem_flatten.mp hword
        have heq : entries=List.range n++List.range n := (List.mem_replicate.mp hentries).2
        rw [heq] at hword
        simp only [List.mem_append,List.mem_range] at hword
        omega
    exact (control_width word).trans ((Nat.add_le_add_right hsmall 1).trans (PlayerSpecificAlgebraicActiveListCost.width_large S).2.2)
  have hc:=PlayerSpecificAlgebraicCallerFrame.cost model rows words S W
    (fun row hrow => (hr row hrow).1) (fun row hrow => (hr row hrow).2) hw
    (PlayerSpecificAlgebraicActiveListCost.width_large S).2.1 (PlayerSpecificAlgebraicActiveListCost.width_large S).1
  apply hc.trans
  apply Nat.mul_le_mul_right (model.rat W)
  simp only [rows,words,List.length_append,List.length_cons,List.length_nil,List.length_ofFn,List.length_range,
    rows_length,List.length_flatten,List.map_replicate,List.sum_replicate,nsmul_eq_mul]
  nlinarith only [Nat.zero_le k,Nat.zero_le m,Nat.zero_le (m*n)]

end Blotto.PlayerSpecificDescriptorProgramFrameCost
