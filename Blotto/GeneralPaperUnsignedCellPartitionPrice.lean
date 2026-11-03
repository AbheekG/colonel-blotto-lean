import Blotto.GeneralPaperSignedCellExtrasPrice

/-! Complete unsigned source-cell partition from the opposite unsigned
CDF, the retained signed summary and every cached option. Actual extras
supply the generic breakpoint/partition premises without replay.
-/
namespace Blotto.GeneralPaperUnsignedCellPartitionPrice
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ) (cdfSummary signedSummary : FixedArrayTable n ℕ)
    (options : FixedArrayTable m ℕ) : GeneralPaperPreparedPartition.Prepared × ℕ :=
  let extras := GeneralPaperUnsignedCellInputPrice.run bits index price W U signedSummary options
  let partition := GeneralPaperEpochPartitionPrice.run bits index price W U cdfSummary extras.1.1
  (partition.1,extras.2+partition.2+64*W)

def profile (price : ℕ → ℕ) (W n m U : ℕ) : ℕ :=
  GeneralPaperUnsignedCellInputPrice.profile price W n m U+GeneralPaperEpochPartitionPrice.profile price W n (n+m) U+64*W

def arithmeticProfile (n m : ℕ) : ℕ :=
  GeneralPaperUnsignedCellInputPrice.arithmeticProfile n m+GeneralPaperEpochPartitionPrice.arithmeticProfile n (n+m)+64

theorem data {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ) (cdfSummary signedSummary : FixedArrayTable n ℕ)
    (options : FixedArrayTable m ℕ) :
    (run bits index price W U cdfSummary signedSummary options).1=GeneralPaperUnsignedPartition.prepare U cdfSummary signedSummary options := by
  unfold run GeneralPaperUnsignedPartition.prepare
  dsimp only
  rw [GeneralPaperEpochPartitionPrice.data,GeneralPaperUnsignedCellInputPrice.data]

theorem bit_work {n m : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W U : ℕ)
    (cdfSummary signedSummary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ)
    (hCDF : ∀ r,cdfSummary.read r<U) (hSigned : ∀ r,signedSummary.read r<2*U) (hOptions : ∀ r,options.read r<U) :
    (run true (fun w => w) price W U cdfSummary signedSummary options).2≤profile price W n m U := by
  have hE := GeneralPaperUnsignedCellInputPrice.bit_work price hMono W U signedSummary options hSigned
  have hP := GeneralPaperEpochPartitionPrice.bit_work price hMono W U cdfSummary
    (GeneralPaperUnsignedCellInputPrice.run true (fun w => w) price W U signedSummary options).1.1 hCDF
    (GeneralPaperUnsignedCellInputPrice.codes true (fun w => w) price W U signedSummary options hSigned hOptions)
  exact Nat.add_le_add_right (Nat.add_le_add hE hP) _

theorem arithmetic_work {n m : ℕ} (U : ℕ) (cdfSummary signedSummary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ)
    (hCDF : ∀ r,cdfSummary.read r<U) (hSigned : ∀ r,signedSummary.read r<2*U) (hOptions : ∀ r,options.read r<U) :
    (run false (fun _ => 1) (fun _ => 1) 1 U cdfSummary signedSummary options).2≤arithmeticProfile n m := by
  have hE := GeneralPaperUnsignedCellInputPrice.arithmetic_work U signedSummary options
  have hP := GeneralPaperEpochPartitionPrice.arithmetic_work U cdfSummary
    (GeneralPaperUnsignedCellInputPrice.run false (fun _ => 1) (fun _ => 1) 1 U signedSummary options).1.1 hCDF
    (GeneralPaperUnsignedCellInputPrice.codes false (fun _ => 1) (fun _ => 1) 1 U signedSummary options hSigned hOptions)
  exact Nat.add_le_add_right (Nat.add_le_add hE hP) _

theorem count_bound {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ)
    (cdfSummary signedSummary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) :
    (run bits index price W U cdfSummary signedSummary options).1.count≤3*n+m+1 := by
  rw [data]
  exact GeneralPaperUnsignedPartition.count_bound U cdfSummary signedSummary options

theorem covers {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ)
    (cdfSummary signedSummary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) :
    GeneralPaperEpochCellInstructions.Covers U (run bits index price W U cdfSummary signedSummary options).1.intervals := by
  rw [data]
  exact GeneralPaperUnsignedPartition.covers U cdfSummary signedSummary options

theorem disjoint {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ)
    (cdfSummary signedSummary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) :
    GeneralPaperEpochCellInstructions.Disjoint (run bits index price W U cdfSummary signedSummary options).1.intervals := by
  rw [data]
  exact GeneralPaperUnsignedPartition.disjoint U cdfSummary signedSummary options

theorem representative_codes {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ)
    (cdfSummary signedSummary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ)
    (r : Fin (run bits index price W U cdfSummary signedSummary options).1.count) :
    (GeneralPaperCellRepresentativePrice.run bits index price W
      (run bits index price W U cdfSummary signedSummary options).1.intervals).1.1.read r<U :=
  GeneralPaperCellRepresentativePrice.prepared_codes bits index price W U cdfSummary
    (GeneralPaperUnsignedCellInputPrice.run bits index price W U signedSummary options).1.1 r

theorem same_data {n m : ℕ} (price : ℕ → ℕ) (W U : ℕ) (cdfSummary signedSummary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) :
    (run true (fun w => w) price W U cdfSummary signedSummary options).1=
      (run false (fun _ => 1) (fun _ => 1) 1 U cdfSummary signedSummary options).1 := by
  rw [data,data]

end Blotto.GeneralPaperUnsignedCellPartitionPrice
