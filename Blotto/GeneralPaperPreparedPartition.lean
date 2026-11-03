import Blotto.GeneralPaperSortedBreakpoints

/-! Actual sorted breakpoint preparation and native adjacent cells. The
source list is sorted once, repetitions are removed once, and the resulting
boundary and cell arrays are retained. Coverage/disjointness are outputs.
-/
namespace Blotto.GeneralPaperPreparedPartition
open GeneralPaperSortedBreakpoints GeneralPaperEpochCellInstructions
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Prepared where
  count : ℕ
  boundaries : FixedArrayTable (count+1) ℕ
  intervals : Cells count

def build (U : ℕ) (points : List ℕ) : Prepared :=
  let values := ordered U points
  let count := values.length-1
  let boundaries : FixedArrayTable (count+1) ℕ := ⟨values.toArray,by
    have hp := ordered_positive U points
    simp only [List.size_toArray]
    dsimp only [values,count]
    omega⟩
  ⟨count,boundaries,GeneralPaperBoundaryCells.cells boundaries⟩

theorem count_eq (U : ℕ) (points : List ℕ) : (build U points).count=(ordered U points).length-1 := rfl

theorem index_bound (U : ℕ) (points : List ℕ) (i : Fin ((build U points).count+1)) :
    i.val<(ordered U points).length := by
  have hi := i.isLt
  have hp := ordered_positive U points
  change i.val<(ordered U points).length-1+1 at hi
  omega

theorem boundary_read (U : ℕ) (points : List ℕ) (i : Fin ((build U points).count+1)) :
    (build U points).boundaries.read i=(ordered U points)[i.val]'(index_bound U points i) := by
  simp only [build,FixedArrayTable.read,List.getElem_toArray]

theorem boundary_member (U : ℕ) (points : List ℕ) (i : Fin ((build U points).count+1)) :
    (build U points).boundaries.read i∈ordered U points := by
  rw [boundary_read]
  exact List.getElem_mem _

theorem boundary_strict (U : ℕ) (points : List ℕ) : StrictMono (build U points).boundaries.read := by
  intro i j hij
  rw [boundary_read,boundary_read]
  exact List.Pairwise.rel_getElem_of_lt (index_bound U points i) (index_bound U points j)
    (ordered_strict U points) (show i.val<j.val from hij)

theorem boundary_represents (U : ℕ) (points : List ℕ) (x : ℕ) (hX : x∈ordered U points) :
    ∃ i, (build U points).boundaries.read i=x := by
  obtain ⟨j,hj,hx⟩ := List.getElem_of_mem hX
  have hp := ordered_positive U points
  let i : Fin ((build U points).count+1) := ⟨j,by rw [count_eq]; omega⟩
  refine ⟨i,?_⟩
  rw [boundary_read]
  exact hx

theorem first_zero (U : ℕ) (points : List ℕ) : (build U points).boundaries.read 0=0 := by
  obtain ⟨j,hj⟩ := boundary_represents U points 0 (zero_mem U points)
  have he := (boundary_strict U points).monotone (show (0:Fin ((build U points).count+1))≤j from Fin.zero_le _)
  rw [hj] at he
  omega

theorem last_upper (U : ℕ) (points : List ℕ) :
    (build U points).boundaries.read (Fin.last (build U points).count)=U := by
  obtain ⟨j,hj⟩ := boundary_represents U points U (upper_mem U points)
  have hJ : j≤Fin.last (build U points).count := by change j.val≤(build U points).count; have := j.isLt; omega
  have he := (boundary_strict U points).monotone hJ
  rw [hj] at he
  have hb := ordered_bound U points _ (boundary_member U points (Fin.last (build U points).count))
  omega

theorem intervals_eq (U : ℕ) (points : List ℕ) :
    (build U points).intervals=GeneralPaperBoundaryCells.cells (build U points).boundaries := rfl

theorem partition_covers (U : ℕ) (points : List ℕ) : Covers U (build U points).intervals := by
  rw [intervals_eq]
  exact GeneralPaperBoundaryCells.covers U _ (first_zero U points) (last_upper U points)

theorem partition_disjoint (U : ℕ) (points : List ℕ) : GeneralPaperEpochCellInstructions.Disjoint (build U points).intervals := by
  rw [intervals_eq]
  exact GeneralPaperBoundaryCells.disjoint _ (boundary_strict U points).monotone

theorem cells_nonempty (U : ℕ) (points : List ℕ) (r : Fin (build U points).count) :
    ((build U points).intervals.read r).1<((build U points).intervals.read r).2 := by
  rw [intervals_eq]
  exact GeneralPaperBoundaryCells.nonempty _ (boundary_strict U points) r

theorem count_bound (U : ℕ) (points : List ℕ) : (build U points).count≤points.length+1 := by
  have he := ordered_length U points
  rw [count_eq]
  omega

theorem threshold_constant (U : ℕ) (points : List ℕ) (x : ℕ) (hX : x∈points) (hBound : x≤U)
    (r : Fin (build U points).count) (i j : ℕ)
    (hI : Contains (build U points).intervals r i) (hJ : Contains (build U points).intervals r j) :
    x≤ i ↔ x≤j := by
  obtain ⟨b,hb⟩ := boundary_represents U points x (point_mem U points x hX hBound)
  have he := GeneralPaperBoundaryCells.threshold_constant (build U points).boundaries
    (boundary_strict U points).monotone r b i j hI hJ
  simpa only [hb] using he

end Blotto.GeneralPaperPreparedPartition
