import Blotto.PlayerSpecificSegmentDrawExecution

/-! Complete segment-draw caller frame retains the original descriptor,
all returned rows, packet counts, selected index and visit counter. -/
namespace Blotto.PlayerSpecificSegmentDrawFrameCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicSegment PlayerSpecificAlgebraicDescriptorBounds
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem cost {N slots : ℕ} (model : RationalCostModel) (root : Candidate) (d : Descriptor N slots) (H K headBits count : ℕ)
    (choice : Fin slots×ℕ) (result : FixedArrayTable N Data) (U : ℕ)
    (hm : HasHeight root.polynomial U) (hml : root.polynomial.length≤4) (he : HasHeight [root.interval.lo,root.interval.hi] U)
    (hd : Bounds root d U) (hr : ∀ j,HasHeight (result.read j) U ∧ (result.read j).length≤3)
    (hN : N≤U) (hslots : slots≤U) (hH : H≤U) (hK : K≤U) (hp : headBits≤U) (hc : count≤U) (hv : choice.2≤U) (hU : 1≤U) :
    price model (PlayerSpecificSegmentDrawExecution.frame root d H K headBits count choice result)≤
      1000*(N+1)*(slots+1)*model.rat (PlayerSpecificAlgebraicComparisonExecution.width U) := by
  let rows:=[root.polynomial,[root.interval.lo,root.interval.hi]]++PlayerSpecificDescriptorProgramExecution.rows d++List.ofFn result.read
  let words:=[N,slots,H,K,headBits,count,choice.1.val,choice.2,1]++List.range N++List.range slots
  let W:=PlayerSpecificAlgebraicComparisonExecution.width U
  have hdesc : ∀ row∈PlayerSpecificDescriptorProgramExecution.rows d,HasHeight row U ∧ row.length≤21 := by
    refine PlayerSpecificDescriptorProgramFrameCost.rows_property d (fun row => HasHeight row U ∧ row.length≤21) ?_ ?_ ?_
    · intro slot; exact ⟨(hd.weights slot).2,by have h:=(hd.weights slot).1.2; omega⟩
    · intro slot j; exact ⟨(hd.first slot j).2,by have h:=(hd.first slot j).1.2; omega⟩
    · intro slot j; exact ⟨(hd.second slot j).2,by have h:=(hd.second slot j).1.2; omega⟩
  have hrows : ∀ row∈rows,HasHeight row U ∧ row.length≤21 := by
    intro row hrow
    simp only [rows,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hrow
    rcases hrow with ((hrow|hrow)|hrow)|hrow
    · rw [hrow]; exact ⟨hm,by omega⟩
    · rw [hrow]; exact ⟨he,by simp⟩
    · exact hdesc row hrow
    · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hrow; exact ⟨(hr j).1,(hr j).2.trans (by decide)⟩
  have hwords : ∀ word∈words,binaryWordWidth word≤W := by
    intro word hword
    have hsmall : word≤U := by
      simp only [words,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range] at hword
      have hs:=choice.1.isLt
      omega
    exact (control_width word).trans ((Nat.add_le_add_right hsmall 1).trans (PlayerSpecificAlgebraicActiveListCost.width_large U).2.2)
  have hf:=PlayerSpecificAlgebraicCallerFrame.cost model rows words U W
    (fun row hrow => (hrows row hrow).1) (fun row hrow => (hrows row hrow).2) hwords
    (PlayerSpecificAlgebraicActiveListCost.width_large U).2.1 (PlayerSpecificAlgebraicActiveListCost.width_large U).1
  apply hf.trans
  apply Nat.mul_le_mul_right (model.rat W)
  simp only [rows,words,List.length_append,List.length_cons,List.length_nil,List.length_ofFn,List.length_range,
    PlayerSpecificDescriptorProgramFrameCost.rows_length]
  nlinarith only [Nat.zero_le N,Nat.zero_le slots,Nat.zero_le (N*slots)]

end Blotto.PlayerSpecificSegmentDrawFrameCost
