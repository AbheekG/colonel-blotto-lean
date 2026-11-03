import Blotto.GeneralPaperCataloguePointPrice

/-! The full source-catalogue partition shares one projected breakpoint
list and one complete ordered-partition construction. Native partition data
and signed-value constancy survive; no code alphabet is enumerated.
-/
namespace Blotto.GeneralPaperCataloguePartitionPrice
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run {n : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W U : ℕ) (summary : FixedArrayTable n ℕ) :
    GeneralPaperPreparedPartition.Prepared × ℕ :=
  let points := GeneralPaperCataloguePointExecution.run bits index primitive W U summary
  let partition := GeneralPaperPartitionExecution.run bits index primitive W U points.1
  (partition.1,points.2+partition.2)

theorem data {n : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W U : ℕ) (summary : FixedArrayTable n ℕ) :
    (run bits index primitive W U summary).1=GeneralPaperTailCataloguePartition.prepare U summary := by
  unfold run GeneralPaperTailCataloguePartition.prepare
  dsimp only
  rw [GeneralPaperPartitionExecution.data,GeneralPaperCataloguePointExecution.data]

def profile (primitive : ℕ → ℕ) (W n U : ℕ) : ℕ :=
  GeneralPaperCataloguePointPrice.profile primitive W n U+GeneralPaperPartitionPrice.profile primitive W n U

def arithmeticProfile (n : ℕ) : ℕ :=
  GeneralPaperCataloguePointPrice.arithmeticProfile n+GeneralPaperPartitionPrice.arithmeticProfile n

theorem bit_work {n : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W U : ℕ) (summary : FixedArrayTable n ℕ)
    (hCodes : ∀ r,summary.read r<2*U) :
    (run true (fun w => w) primitive W U summary).2≤profile primitive W n U := by
  let points := GeneralPaperCataloguePointExecution.run true (fun w => w) primitive W U summary
  have hPoints := GeneralPaperCataloguePointPrice.bit_work primitive hMono W U summary hCodes
  have hPart := GeneralPaperPartitionPrice.bit_work primitive hMono W U points.1
    (GeneralPaperCataloguePointExecution.point_bound true (fun w => w) primitive W U summary hCodes)
  have hPartCap : (GeneralPaperPartitionExecution.run true (fun w => w) primitive W U points.1).2≤
      GeneralPaperPartitionPrice.profile primitive W n U := by
    apply hPart.trans_eq
    rw [GeneralPaperCataloguePointExecution.length]
  exact Nat.add_le_add hPoints hPartCap

theorem arithmetic_work {n : ℕ} (U : ℕ) (summary : FixedArrayTable n ℕ) (hCodes : ∀ r,summary.read r<2*U) :
    (run false (fun _ => 1) (fun _ => 1) 1 U summary).2≤arithmeticProfile n := by
  let points := GeneralPaperCataloguePointExecution.run false (fun _ => 1) (fun _ => 1) 1 U summary
  have hPoints := GeneralPaperCataloguePointPrice.arithmetic_work U summary hCodes
  have hPart := GeneralPaperPartitionPrice.arithmetic_work U points.1
    (GeneralPaperCataloguePointExecution.point_bound false (fun _ => 1) (fun _ => 1) 1 U summary hCodes)
  have hPartCap : (GeneralPaperPartitionExecution.run false (fun _ => 1) (fun _ => 1) 1 U points.1).2≤
      GeneralPaperPartitionPrice.arithmeticProfile n := by
    apply hPart.trans_eq
    rw [GeneralPaperCataloguePointExecution.length]
  exact Nat.add_le_add hPoints hPartCap

theorem same_data {n : ℕ} (primitive : ℕ → ℕ) (W U : ℕ) (summary : FixedArrayTable n ℕ) :
    (run true (fun w => w) primitive W U summary).1=(run false (fun _ => 1) (fun _ => 1) 1 U summary).1 := by
  rw [data,data]

theorem count_bound {n : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W U : ℕ) (summary : FixedArrayTable n ℕ) :
    (run bits index primitive W U summary).1.count≤n+1 := by
  rw [data]
  exact GeneralPaperTailCataloguePartition.count_bound U summary

theorem covers {n : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W U : ℕ) (summary : FixedArrayTable n ℕ) :
    GeneralPaperEpochCellInstructions.Covers U (run bits index primitive W U summary).1.intervals := by
  rw [data]
  exact GeneralPaperTailCataloguePartition.covers U summary

theorem disjoint {n : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W U : ℕ) (summary : FixedArrayTable n ℕ) :
    GeneralPaperEpochCellInstructions.Disjoint (run bits index primitive W U summary).1.intervals := by
  rw [data]
  exact GeneralPaperTailCataloguePartition.disjoint U summary

end Blotto.GeneralPaperCataloguePartitionPrice
