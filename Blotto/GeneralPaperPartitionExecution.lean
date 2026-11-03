import Blotto.GeneralPaperBoundaryCellPrice

/-! One ordered breakpoint list is materialized into its boundary array,
then one adjacent-cell array is filled. The cell count is read from the
returned array descriptor; type/positivity proofs introduce no length pass.
-/
namespace Blotto.GeneralPaperPartitionExecution
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def localWord (W : ℕ) (points : List ℕ) : ℕ := arrayWord W (points.length+2)

def table (data : Array ℕ) (hPositive : 0<data.size) : FixedArrayTable (data.size-1+1) ℕ :=
  ⟨data,by omega⟩

def assemble (bits : Bool) (index primitive : ℕ → ℕ) (W U : ℕ) (points values : List ℕ)
    (hValues : values=GeneralPaperSortedBreakpoints.ordered U points) : GeneralPaperPreparedPartition.Prepared × ℕ :=
  let array := PaperListReferenceArray.run index (if bits then localWord W points else W) values
  let bound := table array.1 (by
    rw [PaperListReferenceArray.size,hValues]
    exact GeneralPaperSortedBreakpoints.ordered_positive U points)
  let cells := GeneralPaperBoundaryCellPrice.run bits index primitive W bound
  (⟨array.1.size-1,bound,cells.1⟩,array.2+cells.2+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a-b) array.1.size 1+64*W)

theorem prepared_ext (p q : GeneralPaperPreparedPartition.Prepared) (hCount : p.count=q.count)
    (hBoundary : HEq p.boundaries q.boundaries) (hCells : HEq p.intervals q.intervals) : p=q := by
  cases p with
  | mk n boundary cells =>
    cases q with
    | mk m other pairs =>
      dsimp only at hCount hBoundary hCells
      cases hCount
      have hb := eq_of_heq hBoundary
      have hc := eq_of_heq hCells
      subst other
      subst pairs
      rfl

theorem cells_heq {n m : ℕ} (a : FixedArrayTable (n+1) ℕ) (b : FixedArrayTable (m+1) ℕ)
    (hCount : n=m) (hArray : HEq a b) : HEq (GeneralPaperBoundaryCells.cells a) (GeneralPaperBoundaryCells.cells b) := by
  cases hCount
  have h := eq_of_heq hArray
  rw [h]

theorem assemble_data (bits : Bool) (index primitive : ℕ → ℕ) (W U : ℕ) (points values : List ℕ)
    (hValues : values=GeneralPaperSortedBreakpoints.ordered U points) :
    (assemble bits index primitive W U points values hValues).1=GeneralPaperPreparedPartition.build U points := by
  subst values
  let p := (assemble bits index primitive W U points (GeneralPaperSortedBreakpoints.ordered U points) rfl).1
  let q := GeneralPaperPreparedPartition.build U points
  have hCount : p.count=q.count := by
    change (PaperListReferenceArray.run index (if bits then localWord W points else W)
      (GeneralPaperSortedBreakpoints.ordered U points)).1.size-1=(GeneralPaperSortedBreakpoints.ordered U points).length-1
    rw [PaperListReferenceArray.size]
  have hBoundary : HEq p.boundaries q.boundaries := by
    apply GeneralPaperSelectedRankPrice.array_heq
    exact PaperListReferenceArray.data index _ _
  have hLeft : p.intervals=GeneralPaperBoundaryCells.cells p.boundaries :=
    GeneralPaperBoundaryCellPrice.data bits index primitive W _
  have hRight : q.intervals=GeneralPaperBoundaryCells.cells q.boundaries :=
    GeneralPaperPreparedPartition.intervals_eq U points
  apply prepared_ext p q hCount hBoundary
  rw [hLeft,hRight]
  exact cells_heq p.boundaries q.boundaries hCount hBoundary

def run (bits : Bool) (index primitive : ℕ → ℕ) (W U : ℕ) (points : List ℕ) : GeneralPaperPreparedPartition.Prepared × ℕ :=
  let ordered := GeneralPaperNaturalOrderPrice.run primitive (if bits then localWord W points else W) U points
  let prepared := assemble bits index primitive W U points ordered.1
    (GeneralPaperNaturalOrderPrice.data primitive (if bits then localWord W points else W) U points)
  (prepared.1,ordered.2+prepared.2)

theorem data (bits : Bool) (index primitive : ℕ → ℕ) (W U : ℕ) (points : List ℕ) :
    (run bits index primitive W U points).1=GeneralPaperPreparedPartition.build U points :=
  assemble_data bits index primitive W U points _ (GeneralPaperNaturalOrderPrice.data _ _ _ _)

theorem count_bound (bits : Bool) (index primitive : ℕ → ℕ) (W U : ℕ) (points : List ℕ) :
    (run bits index primitive W U points).1.count≤points.length+1 := by
  rw [data]
  exact GeneralPaperPreparedPartition.count_bound U points

theorem covers (bits : Bool) (index primitive : ℕ → ℕ) (W U : ℕ) (points : List ℕ) :
    GeneralPaperEpochCellInstructions.Covers U (run bits index primitive W U points).1.intervals := by
  rw [data]
  exact GeneralPaperPreparedPartition.partition_covers U points

theorem disjoint (bits : Bool) (index primitive : ℕ → ℕ) (W U : ℕ) (points : List ℕ) :
    GeneralPaperEpochCellInstructions.Disjoint (run bits index primitive W U points).1.intervals := by
  rw [data]
  exact GeneralPaperPreparedPartition.partition_disjoint U points

theorem boundary_bound (bits : Bool) (index primitive : ℕ → ℕ) (W U : ℕ) (points : List ℕ)
    (i : Fin ((run bits index primitive W U points).1.count+1)) :
    (run bits index primitive W U points).1.boundaries.read i≤U := by
  have bounded (p : GeneralPaperPreparedPartition.Prepared) (hp : p=GeneralPaperPreparedPartition.build U points)
      (j : Fin (p.count+1)) : p.boundaries.read j≤U := by
    subst p
    exact GeneralPaperSortedBreakpoints.ordered_bound U points _ (GeneralPaperPreparedPartition.boundary_member U points j)
  exact bounded _ (data bits index primitive W U points) i

end Blotto.GeneralPaperPartitionExecution
