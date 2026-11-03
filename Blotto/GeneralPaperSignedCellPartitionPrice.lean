import Blotto.GeneralPaperUnsignedCellPartitionPrice

/-! Complete signed source-cell partition. Both copies of thresholds/bids
and the sign boundary feed one native partition over twice the unsigned
alphabet. The doubled alphabet limit is computed once and priced.
-/
namespace Blotto.GeneralPaperSignedCellPartitionPrice
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ) (summary : FixedArrayTable n ℕ)
    (options : FixedArrayTable m ℕ) : GeneralPaperPreparedPartition.Prepared × ℕ :=
  let positions := GeneralPaperSignedCellPositionsPrice.run bits index price W U summary
  let extras := GeneralPaperSignedCellExtrasPrice.run bits index price W U options
  let limit := 2*U
  let partition := GeneralPaperEpochPartitionPrice.run bits index price W limit positions.1.1 extras.1.1
  (partition.1,positions.2+extras.2+partition.2+
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 2 U+64*W)

def profile (price : ℕ → ℕ) (W n m U : ℕ) : ℕ :=
  GeneralPaperSignedCellPositionsPrice.profile price W n U+GeneralPaperSignedCellExtrasPrice.profile price W m U+
    GeneralPaperEpochPartitionPrice.profile price W (2*n) (2*m+1) (2*U)+2*price (GeneralPaperCataloguePointOperands.width U)+64*W

def arithmeticProfile (n m : ℕ) : ℕ :=
  GeneralPaperSignedCellPositionsPrice.arithmeticProfile n+GeneralPaperSignedCellExtrasPrice.arithmeticProfile m+
    GeneralPaperEpochPartitionPrice.arithmeticProfile (2*n) (2*m+1)+66

theorem data {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ) (summary : FixedArrayTable n ℕ)
    (options : FixedArrayTable m ℕ) :
    (run bits index price W U summary options).1=GeneralPaperSignedPartition.prepare U summary options := by
  unfold run GeneralPaperSignedPartition.prepare
  dsimp only
  rw [GeneralPaperEpochPartitionPrice.data,GeneralPaperSignedCellPositionsPrice.data,GeneralPaperSignedCellExtrasPrice.data]

theorem limit_work (price : ℕ → ℕ) (hMono : Monotone price) (U : ℕ) :
    GeneralPaperNaturalPrimitivePrice.binary price (fun a b => a*b) 2 U≤2*price (GeneralPaperCataloguePointOperands.width U) :=
  (GeneralPaperNaturalPrimitivePrice.binary_le price hMono (fun a b => a*b) 2 U (GeneralPaperCataloguePointOperands.magnitude U)
    (by unfold GeneralPaperCataloguePointOperands.magnitude; omega)
    (by unfold GeneralPaperCataloguePointOperands.magnitude; omega)
    (by unfold GeneralPaperCataloguePointOperands.magnitude; omega)).trans
      (Nat.mul_le_mul_left 2 (hMono (GeneralPaperCataloguePointOperands.word_bound U)))

theorem bit_work {n m : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W U : ℕ)
    (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ)
    (hSummary : ∀ r,summary.read r<U) (hOptions : ∀ r,options.read r<U) :
    (run true (fun w => w) price W U summary options).2≤profile price W n m U := by
  have hP := GeneralPaperSignedCellPositionsPrice.bit_work price hMono W U summary hSummary
  have hE := GeneralPaperSignedCellExtrasPrice.bit_work price hMono W U options hOptions
  have hPart := GeneralPaperEpochPartitionPrice.bit_work price hMono W (2*U)
    (GeneralPaperSignedCellPositionsPrice.run true (fun w => w) price W U summary).1.1
    (GeneralPaperSignedCellExtrasPrice.run true (fun w => w) price W U options).1.1
    (GeneralPaperSignedCellPositionsPrice.codes true (fun w => w) price W U summary hSummary)
    (GeneralPaperSignedCellExtrasPrice.codes true (fun w => w) price W U options hOptions)
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hP hE) hPart) (limit_work price hMono U)) _

theorem arithmetic_work {n m : ℕ} (U : ℕ) (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ)
    (hSummary : ∀ r,summary.read r<U) (hOptions : ∀ r,options.read r<U) :
    (run false (fun _ => 1) (fun _ => 1) 1 U summary options).2≤arithmeticProfile n m := by
  have hP := GeneralPaperSignedCellPositionsPrice.arithmetic_work U summary
  have hE := GeneralPaperSignedCellExtrasPrice.arithmetic_work U options
  have hPart := GeneralPaperEpochPartitionPrice.arithmetic_work (2*U)
    (GeneralPaperSignedCellPositionsPrice.run false (fun _ => 1) (fun _ => 1) 1 U summary).1.1
    (GeneralPaperSignedCellExtrasPrice.run false (fun _ => 1) (fun _ => 1) 1 U options).1.1
    (GeneralPaperSignedCellPositionsPrice.codes false (fun _ => 1) (fun _ => 1) 1 U summary hSummary)
    (GeneralPaperSignedCellExtrasPrice.codes false (fun _ => 1) (fun _ => 1) 1 U options hOptions)
  have hCost : (run false (fun _ => 1) (fun _ => 1) 1 U summary options).2=
      (GeneralPaperSignedCellPositionsPrice.run false (fun _ => 1) (fun _ => 1) 1 U summary).2+
      (GeneralPaperSignedCellExtrasPrice.run false (fun _ => 1) (fun _ => 1) 1 U options).2+
      (GeneralPaperEpochPartitionPrice.run false (fun _ => 1) (fun _ => 1) 1 (2*U)
        (GeneralPaperSignedCellPositionsPrice.run false (fun _ => 1) (fun _ => 1) 1 U summary).1.1
        (GeneralPaperSignedCellExtrasPrice.run false (fun _ => 1) (fun _ => 1) 1 U options).1.1).2+66 := by
    unfold run
    dsimp only
    simp only [GeneralPaperNaturalPrimitivePrice.binary]
  rw [hCost]
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hP hE) hPart) 66

theorem count_bound {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ)
    (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) :
    (run bits index price W U summary options).1.count≤4*n+2*m+2 := by
  rw [data]
  exact GeneralPaperSignedPartition.count_bound U summary options

theorem covers {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ)
    (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) :
    GeneralPaperEpochCellInstructions.Covers (2*U) (run bits index price W U summary options).1.intervals := by
  rw [data]
  exact GeneralPaperSignedPartition.covers U summary options

theorem disjoint {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ)
    (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) :
    GeneralPaperEpochCellInstructions.Disjoint (run bits index price W U summary options).1.intervals := by
  rw [data]
  exact GeneralPaperSignedPartition.disjoint U summary options

theorem representative_codes {n m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ)
    (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ)
    (r : Fin (run bits index price W U summary options).1.count) :
    (GeneralPaperCellRepresentativePrice.run bits index price W (run bits index price W U summary options).1.intervals).1.1.read r<2*U :=
  GeneralPaperCellRepresentativePrice.prepared_codes bits index price W (2*U)
    (GeneralPaperSignedCellPositionsPrice.run bits index price W U summary).1.1
    (GeneralPaperSignedCellExtrasPrice.run bits index price W U options).1.1 r

theorem same_data {n m : ℕ} (price : ℕ → ℕ) (W U : ℕ) (summary : FixedArrayTable n ℕ) (options : FixedArrayTable m ℕ) :
    (run true (fun w => w) price W U summary options).1=(run false (fun _ => 1) (fun _ => 1) 1 U summary options).1 := by
  rw [data,data]

end Blotto.GeneralPaperSignedCellPartitionPrice
