import Blotto.GeneralPaperPreparedPartition

/-! Materialize the left endpoint of each prepared nonempty cell. These
are actual valid alphabet codes, so cell queries need no search at run time.
-/
namespace Blotto.GeneralPaperCellRepresentatives
open GeneralPaperEpochCellInstructions
set_option autoImplicit false

def build {n : ℕ} (cells : Cells n) : FixedArrayTable n ℕ × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun r => ((cells.read r).1,8))

theorem read_build {n : ℕ} (cells : Cells n) (r : Fin n) :
    (build cells).1.read r=(cells.read r).1 := by
  rw [build,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]

theorem work {n : ℕ} (cells : Cells n) : (build cells).2=50*n+18 := by
  rw [build,PaperIndexedArrayConstruction.run_work,GeneralPaperEpochLevelArray.overhead]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  omega

theorem upper_bound (U : ℕ) (points : List ℕ) (r : Fin (GeneralPaperPreparedPartition.build U points).count) :
    ((GeneralPaperPreparedPartition.build U points).intervals.read r).2≤U := by
  rw [GeneralPaperPreparedPartition.intervals_eq,GeneralPaperBoundaryCells.read_cells]
  exact GeneralPaperSortedBreakpoints.ordered_bound U points _
    (GeneralPaperPreparedPartition.boundary_member U points r.succ)

theorem contains_representative (U : ℕ) (points : List ℕ)
    (r : Fin (GeneralPaperPreparedPartition.build U points).count) :
    Contains (GeneralPaperPreparedPartition.build U points).intervals r
      ((build (GeneralPaperPreparedPartition.build U points).intervals).1.read r) := by
  rw [read_build]
  exact ⟨le_rfl,GeneralPaperPreparedPartition.cells_nonempty U points r⟩

theorem representative_bound (U : ℕ) (points : List ℕ)
    (r : Fin (GeneralPaperPreparedPartition.build U points).count) :
    (build (GeneralPaperPreparedPartition.build U points).intervals).1.read r<U := by
  have hc := contains_representative U points r
  have hb := upper_bound U points r
  exact lt_of_lt_of_le hc.2 hb

theorem contains_bound (U : ℕ) (points : List ℕ)
    (r : Fin (GeneralPaperPreparedPartition.build U points).count) (i : ℕ)
    (h : Contains (GeneralPaperPreparedPartition.build U points).intervals r i) : i<U :=
  lt_of_lt_of_le h.2 (upper_bound U points r)

end Blotto.GeneralPaperCellRepresentatives
