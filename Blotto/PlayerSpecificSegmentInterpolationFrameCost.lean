import Blotto.PlayerSpecificSegmentInterpolationExecution

/-! Complete interpolation source frames include both selected input
arrays, returned allocation rows, cached scalars and finite indices. -/
namespace Blotto.PlayerSpecificSegmentInterpolationFrameCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem cost {N slots : ℕ} (model : RationalCostModel) (root : Candidate) (first second result : FixedArrayTable N Data)
    (slot : Fin slots) (q complement : ℚ) (left right : Data) (U : ℕ)
    (hm : HasHeight root.polynomial U) (hml : root.polynomial.length≤4) (he : HasHeight [root.interval.lo,root.interval.hi] U)
    (hq : RationalHeight q U) (hc : RationalHeight complement U)
    (hl : HasHeight left U ∧ left.length≤3) (hr : HasHeight right U ∧ right.length≤3)
    (hp : ∀ j,HasHeight (first.read j) U ∧ (first.read j).length≤3)
    (hQ : ∀ j,HasHeight (second.read j) U ∧ (second.read j).length≤3)
    (hy : ∀ j,HasHeight (result.read j) U ∧ (result.read j).length≤3)
    (hN : N≤U) (hslots : slots≤U) (_hU : 1≤U) :
    price model (PlayerSpecificSegmentInterpolationExecution.frame root first second result slot q complement left right)≤
      1000*(N+1)*model.rat (PlayerSpecificAlgebraicComparisonExecution.width U) := by
  let rows:=[root.polynomial,[root.interval.lo,root.interval.hi],[q,complement],left,right]++List.ofFn first.read++List.ofFn second.read++List.ofFn result.read
  let words:=[N,slots,slot.val,slot.val,1]++List.range N++List.range N++List.range N
  let W:=PlayerSpecificAlgebraicComparisonExecution.width U
  have hrows : ∀ row∈rows,HasHeight row U ∧ row.length≤21 := by
    intro row hrow
    simp only [rows,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hrow
    rcases hrow with (((hrow|hrow|hrow|hrow|hrow)|hrow)|hrow)|hrow
    · rw [hrow]; exact ⟨hm,by omega⟩
    · rw [hrow]; exact ⟨he,by simp⟩
    · rw [hrow]; exact ⟨cons_height hq (cons_height hc (nil_height _)),by simp⟩
    · rw [hrow]; exact ⟨hl.1,hl.2.trans (by decide)⟩
    · rw [hrow]; exact ⟨hr.1,hr.2.trans (by decide)⟩
    · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hrow; exact ⟨(hp j).1,(hp j).2.trans (by decide)⟩
    · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hrow; exact ⟨(hQ j).1,(hQ j).2.trans (by decide)⟩
    · obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hrow; exact ⟨(hy j).1,(hy j).2.trans (by decide)⟩
  have hwords : ∀ word∈words,binaryWordWidth word≤W := by
    intro word hword
    have hsmall : word≤U := by
      simp only [words,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_range] at hword
      have hs:=slot.isLt
      omega
    exact (control_width word).trans ((Nat.add_le_add_right hsmall 1).trans (PlayerSpecificAlgebraicActiveListCost.width_large U).2.2)
  have hf:=PlayerSpecificAlgebraicCallerFrame.cost model rows words U W
    (fun row hrow => (hrows row hrow).1) (fun row hrow => (hrows row hrow).2) hwords
    (PlayerSpecificAlgebraicActiveListCost.width_large U).2.1 (PlayerSpecificAlgebraicActiveListCost.width_large U).1
  apply hf.trans
  apply Nat.mul_le_mul_right (model.rat W)
  simp only [rows,words,List.length_append,List.length_cons,List.length_nil,List.length_ofFn,List.length_range]
  omega

end Blotto.PlayerSpecificSegmentInterpolationFrameCost
