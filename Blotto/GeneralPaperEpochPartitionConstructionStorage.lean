import Blotto.GeneralPaperEpochPointStorage

/-! Complete native epoch partitions join the constructed breakpoint lists
with sorting, packing and cell fills at the actual derived local word.
Array metadata, full returned partition and complete scratch remain live. -/
namespace Blotto.GeneralPaperEpochPartitionConstructionStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem points_bound {n m : ℕ} (model : RationalCostModel) (W U : ℕ)
    (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ)
    (hp : ∀ i,positions.read i<U) (he : ∀ i,extras.read i≤U) :
    ∀ x∈GeneralPaperEpochPartition.points positions extras,x≤U := by
  intro x hx
  exact GeneralPaperEpochPointExecution.points_bound true (fun w => w) model.rat W U positions extras hp he x
    (by rw [GeneralPaperEpochPointExecution.data]; exact hx)

def window {n m : ℕ} (model : RationalCostModel) (W U usedP usedE copied count : ℕ)
    (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ)
    (hc : count≤(GeneralPaperEpochPartition.prepare U positions extras).count) : ℕ :=
  GeneralPaperEpochPointStorage.window model W usedP usedE positions extras+
    GeneralPaperPartitionConstructionStorage.window model W U (GeneralPaperEpochPartition.points positions extras) copied count hc+
    GeneralPaperEncodedPartitionStorage.footprint W (GeneralPaperEpochPartitionPrice.run true (fun w => w) model.rat W U positions extras).1+
    fields W [U,n,m]+(GeneralPaperEpochPartitionPrice.run true (fun w => w) model.rat W U positions extras).2+256*W

def profile (model : RationalCostModel) (W U n m : ℕ) : ℕ :=
  GeneralPaperEpochPointStorage.profile model W U n m+GeneralPaperPartitionConstructionStorage.profile model W U (2*n+m)+
    GeneralPaperEncodedPartitionStorage.profile W (natBits U) (2*n+m+1)+fields W [U,n,m]+
    GeneralPaperEpochPartitionPrice.profile model.rat W n m U+256*W

theorem returned {n m : ℕ} (model : RationalCostModel) (W U : ℕ)
    (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ) :
    GeneralPaperEncodedPartitionStorage.footprint W (GeneralPaperEpochPartitionPrice.run true (fun w => w) model.rat W U positions extras).1≤
      GeneralPaperEncodedPartitionStorage.profile W (natBits U) (2*n+m+1) := by
  rw [GeneralPaperEpochPartitionPrice.data]
  exact GeneralPaperEncodedPartitionStorage.constructed W (natBits U) (2*n+m+1) U
    (GeneralPaperEpochPartition.points positions extras) (GeneralPaperEpochPartition.count_bound U positions extras) (Nat.le_refl _)

theorem bounded {n m : ℕ} (model : RationalCostModel) (W U usedP usedE copied count : ℕ)
    (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ)
    (hp : ∀ i,positions.read i<U) (he : ∀ i,extras.read i≤U)
    (hc : count≤(GeneralPaperEpochPartition.prepare U positions extras).count) :
    window model W U usedP usedE copied count positions extras hc≤profile model W U n m := by
  have hpoints := GeneralPaperEpochPointStorage.bounded model W U usedP usedE positions extras hp he
  have hpart := GeneralPaperPartitionConstructionStorage.bounded model W U (GeneralPaperEpochPartition.points positions extras)
    (points_bound model W U positions extras hp he) copied count hc
  rw [GeneralPaperEpochPartition.points_length] at hpart
  have hr := returned model W U positions extras
  have hw := GeneralPaperEpochPartitionPrice.bit_work model.rat model.monotone W U positions extras hp he
  unfold window profile
  omega

theorem local_word {n m : ℕ} (W : ℕ) (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ) :
    GeneralPaperPartitionExecution.localWord W (GeneralPaperEpochPartition.points positions extras)=
      GeneralPaperSummaryArrayExecution.arrayWord W (2*n+m+2) := by
  unfold GeneralPaperPartitionExecution.localWord
  rw [GeneralPaperEpochPartition.points_length]

end Blotto.GeneralPaperEpochPartitionConstructionStorage
