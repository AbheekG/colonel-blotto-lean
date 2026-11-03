import Blotto.GeneralPaperEpochPointPrice

/-! Complete native epoch partition from retained position/extra arrays.
One breakpoint builder feeds the existing stable-sort/dedup/boundary/cell
constructor, with all local premises derived from the returned input list.
-/
namespace Blotto.GeneralPaperEpochPartitionPrice
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ)
    (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ) : GeneralPaperPreparedPartition.Prepared × ℕ :=
  let points := GeneralPaperEpochPointExecution.run bits index price W positions extras
  let partition := GeneralPaperPartitionExecution.run bits index price W U points.1
  (partition.1,points.2+partition.2+64*W)

def profile (price : ℕ → ℕ) (W n m U : ℕ) : ℕ :=
  GeneralPaperEpochPointPrice.profile price W n m U+GeneralPaperPartitionPrice.profile price W (2*n+m) U+64*W

def arithmeticProfile (n m : ℕ) : ℕ :=
  GeneralPaperEpochPointPrice.arithmeticProfile n m+GeneralPaperPartitionPrice.arithmeticProfile (2*n+m)+64

theorem data {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ)
    (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ) :
    (run bits index price W U positions extras).1=GeneralPaperEpochPartition.prepare U positions extras := by
  unfold run
  dsimp only
  rw [GeneralPaperPartitionExecution.data,GeneralPaperEpochPointExecution.data]
  rfl

theorem bit_work {n m : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W U : ℕ)
    (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ)
    (hPositions : ∀ r,positions.read r<U) (hExtras : ∀ r,extras.read r≤U) :
    (run true (fun w => w) price W U positions extras).2≤profile price W n m U := by
  have hP := GeneralPaperEpochPointPrice.bit_work price hMono W U positions extras hPositions
  have hPart := GeneralPaperPartitionPrice.bit_work price hMono W U
    (GeneralPaperEpochPointExecution.run true (fun w => w) price W positions extras).1
    (GeneralPaperEpochPointExecution.points_bound true (fun w => w) price W U positions extras hPositions hExtras)
  have hN := GeneralPaperEpochPointExecution.length true (fun w => w) price W positions extras
  have hBound := hPart.trans_eq (congrArg (fun N => GeneralPaperPartitionPrice.profile price W N U) hN)
  exact Nat.add_le_add_right (Nat.add_le_add hP hBound) _

theorem arithmetic_work {n m : ℕ} (U : ℕ) (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ)
    (hPositions : ∀ r,positions.read r<U) (hExtras : ∀ r,extras.read r≤U) :
    (run false (fun _ => 1) (fun _ => 1) 1 U positions extras).2≤arithmeticProfile n m := by
  have hP := GeneralPaperEpochPointPrice.arithmetic_work positions extras
  have hPart := GeneralPaperPartitionPrice.arithmetic_work U
    (GeneralPaperEpochPointExecution.run false (fun _ => 1) (fun _ => 1) 1 positions extras).1
    (GeneralPaperEpochPointExecution.points_bound false (fun _ => 1) (fun _ => 1) 1 U positions extras hPositions hExtras)
  have hN := GeneralPaperEpochPointExecution.length false (fun _ => 1) (fun _ => 1) 1 positions extras
  have hBound := hPart.trans_eq (congrArg GeneralPaperPartitionPrice.arithmeticProfile hN)
  exact Nat.add_le_add_right (Nat.add_le_add hP hBound) _

theorem count_bound {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ)
    (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ) :
    (run bits index price W U positions extras).1.count≤2*n+m+1 := by
  rw [data]
  exact GeneralPaperEpochPartition.count_bound U positions extras

theorem covers {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ)
    (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ) :
    GeneralPaperEpochCellInstructions.Covers U (run bits index price W U positions extras).1.intervals := by
  rw [data]
  exact GeneralPaperEpochPartition.covers U positions extras

theorem disjoint {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ)
    (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ) :
    GeneralPaperEpochCellInstructions.Disjoint (run bits index price W U positions extras).1.intervals := by
  rw [data]
  exact GeneralPaperEpochPartition.disjoint U positions extras

theorem cell_bounds {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ)
    (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ)
    (r : Fin (run bits index price W U positions extras).1.count) :
    (((run bits index price W U positions extras).1.intervals).read r).1<
      (((run bits index price W U positions extras).1.intervals).read r).2 ∧
    (((run bits index price W U positions extras).1.intervals).read r).2≤U := by
  have native (p : GeneralPaperPreparedPartition.Prepared) (hp : p=GeneralPaperEpochPartition.prepare U positions extras)
      (cell : Fin p.count) : (p.intervals.read cell).1<(p.intervals.read cell).2 ∧ (p.intervals.read cell).2≤U := by
    subst p
    change Fin (GeneralPaperPreparedPartition.build U (GeneralPaperEpochPartition.points positions extras)).count at cell
    exact ⟨GeneralPaperPreparedPartition.cells_nonempty U _ cell,GeneralPaperCellRepresentatives.upper_bound U _ cell⟩
  exact native _ (data bits index price W U positions extras) r

theorem same_data {n m : ℕ} (price : ℕ → ℕ) (W U : ℕ)
    (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ) :
    (run true (fun w => w) price W U positions extras).1=(run false (fun _ => 1) (fun _ => 1) 1 U positions extras).1 := by
  rw [data,data]

end Blotto.GeneralPaperEpochPartitionPrice
