import Blotto.GeneralPaperCataloguePointStorage

/-! Actual source-catalogue partition: signed-code projection once, one
ordered-partition constructor and retained native return/caller values.
The native local array word is retained inside the partition bound. -/
namespace Blotto.GeneralPaperCataloguePartitionStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def metadata (W U n : ℕ) : ℕ := fields W [U,n,n+1]

theorem metadata_bound (W U n : ℕ) : metadata W U n≤3*(natBits U+natBits (n+1)+W)+32*W := by
  apply fields_bound W (natBits U+natBits (n+1))
  intro x hx
  have hn := binaryWordWidth_mono (show n≤n+1 by omega)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl <;> unfold natBits <;> omega

def window {n : ℕ} (model : RationalCostModel) (W U used copied count : ℕ) (summary : FixedArrayTable n ℕ)
    (hc : count≤(GeneralPaperTailCataloguePartition.prepare U summary).count) : ℕ :=
  GeneralPaperCataloguePointStorage.window model W U used summary+
    GeneralPaperPartitionConstructionStorage.window model W U (GeneralPaperTailCataloguePartition.points U summary) copied count hc+
    GeneralPaperEncodedPartitionStorage.footprint W
      (GeneralPaperCataloguePartitionPrice.run true (fun w => w) model.rat W U summary).1+
    metadata W U n+256*W

def profile (model : RationalCostModel) (W U n : ℕ) : ℕ :=
  GeneralPaperCataloguePointStorage.profile model W U n+GeneralPaperPartitionConstructionStorage.profile model W U n+
    GeneralPaperEncodedPartitionStorage.profile W (natBits U) (n+1)+
      3*(natBits U+natBits (n+1)+W)+32*W+256*W

theorem bounded {n : ℕ} (model : RationalCostModel) (W U used copied count : ℕ) (summary : FixedArrayTable n ℕ)
    (hc : count≤(GeneralPaperTailCataloguePartition.prepare U summary).count) (hCodes : ∀ r,summary.read r<2*U) :
    window model W U used copied count summary hc≤profile model W U n := by
  have hp := GeneralPaperCataloguePointStorage.bounded model W U used summary hCodes
  have hbound : ∀ x∈GeneralPaperTailCataloguePartition.points U summary,x≤U := by
    intro x hx
    apply GeneralPaperCataloguePointExecution.point_bound true (fun w => w) model.rat W U summary hCodes x
    rw [GeneralPaperCataloguePointExecution.data]
    exact hx
  have hpart := GeneralPaperPartitionConstructionStorage.bounded model W U
    (GeneralPaperTailCataloguePartition.points U summary) hbound copied count hc
  rw [GeneralPaperTailCataloguePartition.points_length] at hpart
  have hr := GeneralPaperEncodedPartitionStorage.constructed W (natBits U) (n+1) U
    (GeneralPaperTailCataloguePartition.points U summary) (by
      change (GeneralPaperTailCataloguePartition.prepare U summary).count≤n+1
      exact GeneralPaperTailCataloguePartition.count_bound U summary) (Nat.le_refl _)
  have hm := metadata_bound W U n
  unfold window profile
  rw [GeneralPaperCataloguePartitionPrice.data]
  change _≤GeneralPaperCataloguePointStorage.profile model W U n+
    GeneralPaperPartitionConstructionStorage.profile model W U n+
    GeneralPaperEncodedPartitionStorage.profile W (natBits U) (n+1)+
    3*(natBits U+natBits (n+1)+W)+32*W+256*W
  change GeneralPaperEncodedPartitionStorage.footprint W (GeneralPaperTailCataloguePartition.prepare U summary)≤_ at hr
  omega

theorem local_word {n : ℕ} (W U : ℕ) (summary : FixedArrayTable n ℕ) :
    GeneralPaperPartitionExecution.localWord W (GeneralPaperTailCataloguePartition.points U summary)=
      GeneralPaperSummaryArrayExecution.arrayWord W (n+2) := by
  unfold GeneralPaperPartitionExecution.localWord
  rw [GeneralPaperTailCataloguePartition.points_length]

theorem source_payload (a : GeneralPaperCodeAlphabet.Alphabet) : natBits (2*(8*a.C))≤64+8*a.lambda := by
  have he : 2*(8*a.C)=2^(a.lambda+1) := by rw [pow_succ,←a.dyadic]; ring
  have h := GeneralPaperNatPowerOperands.power_width 2 (a.lambda+1)
  have h2 : binaryWordWidth 2=2 := by decide
  rw [h2] at h
  unfold natBits
  rw [he]
  omega

theorem source_returned {n : ℕ} (model : RationalCostModel) (W : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet)
    (summary : FixedArrayTable n ℕ) :
    GeneralPaperEncodedPartitionStorage.footprint W
      (GeneralPaperCataloguePartitionPrice.run true (fun w => w) model.rat W (8*a.C) summary).1≤
      GeneralPaperEncodedPartitionStorage.profile W (64+8*a.lambda) (n+1) := by
  rw [GeneralPaperCataloguePartitionPrice.data]
  apply GeneralPaperEncodedPartitionStorage.constructed W (64+8*a.lambda) (n+1) (8*a.C)
    (GeneralPaperTailCataloguePartition.points (8*a.C) summary)
    (GeneralPaperTailCataloguePartition.count_bound (8*a.C) summary)
  have h := source_payload a
  have hm := binaryWordWidth_mono (show 8*a.C≤2*(8*a.C) by omega)
  unfold natBits at h
  omega

end Blotto.GeneralPaperCataloguePartitionStorage
