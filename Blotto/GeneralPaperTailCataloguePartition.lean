import Blotto.GeneralPaperCatalogueSlots

/-! The catalogue partition uses only projected signed-summary successors.
Its O(summary-size) cells cover the whole code interval. Separately rounded
positive/negative tail values are constant on each cell for every current
prefix array. Sorting and its full bit/storage prices remain a source join.
-/
namespace Blotto.GeneralPaperTailCataloguePartition
open GeneralPaperEpochCellInstructions
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
set_option autoImplicit false
set_option maxHeartbeats 3500000

def points {n : ℕ} (U : ℕ) (summary : FixedArrayTable n ℕ) : List ℕ :=
  summary.data.toList.map (fun x => GeneralPaperSignedUpdatePlan.project U x+1)

def prepare {n : ℕ} (U : ℕ) (summary : FixedArrayTable n ℕ) : GeneralPaperPreparedPartition.Prepared :=
  GeneralPaperPreparedPartition.build U (points U summary)

theorem points_length {n : ℕ} (U : ℕ) (summary : FixedArrayTable n ℕ) : (points U summary).length=n := by
  simp only [points,List.length_map,Array.length_toList,summary.size]

theorem successor_mem {n : ℕ} (U : ℕ) (summary : FixedArrayTable n ℕ) (r : Fin n) :
    GeneralPaperSignedUpdatePlan.project U (summary.read r)+1∈points U summary :=
  List.mem_map.mpr ⟨summary.read r,GeneralPaperEpochPartition.read_mem summary r,rfl⟩

theorem count_bound {n : ℕ} (U : ℕ) (summary : FixedArrayTable n ℕ) : (prepare U summary).count≤n+1 := by
  have he := GeneralPaperPreparedPartition.count_bound U (points U summary)
  simpa only [prepare,points_length] using he

theorem covers {n : ℕ} (U : ℕ) (summary : FixedArrayTable n ℕ) : Covers U (prepare U summary).intervals :=
  GeneralPaperPreparedPartition.partition_covers U (points U summary)

theorem disjoint {n : ℕ} (U : ℕ) (summary : FixedArrayTable n ℕ) :
    GeneralPaperEpochCellInstructions.Disjoint (prepare U summary).intervals :=
  GeneralPaperPreparedPartition.partition_disjoint U (points U summary)

theorem projected_test_constant {n : ℕ} (U : ℕ) (summary : FixedArrayTable n ℕ) (a : Fin n)
    (hCode : summary.read a<2*U) (r : Fin (prepare U summary).count) (i j : ℕ)
    (hI : Contains (prepare U summary).intervals r i) (hJ : Contains (prepare U summary).intervals r j) :
    GeneralPaperSignedUpdatePlan.project U (summary.read a)< i ↔ GeneralPaperSignedUpdatePlan.project U (summary.read a)< j := by
  have hb := GeneralPaperUnsignedPartition.project_bound U _ hCode
  have he := GeneralPaperPreparedPartition.threshold_constant U (points U summary)
    (GeneralPaperSignedUpdatePlan.project U (summary.read a)+1) (successor_mem U summary a) (by omega) r i j hI hJ
  omega

theorem tail_counts_constant (k U : ℕ) (summary : Summary k) (preparedPrefix : Prefix k)
    (hMono : Monotone summary.read) (hCodes : ∀ a, summary.read a<2*U)
    (r : Fin (prepare U summary).count) (i j : ℕ)
    (hI : Contains (prepare U summary).intervals r i) (hJ : Contains (prepare U summary).intervals r j) :
    GeneralPaperRankedInterval.referenceCount k summary preparedPrefix i U=
      GeneralPaperRankedInterval.referenceCount k summary preparedPrefix j U ∧
    GeneralPaperRankedInterval.referenceCount k summary preparedPrefix (U+i) (2*U)=
      GeneralPaperRankedInterval.referenceCount k summary preparedPrefix (U+j) (2*U) := by
  have hi := GeneralPaperCellRepresentatives.contains_bound U (points U summary) r i hI
  have hj := GeneralPaperCellRepresentatives.contains_bound U (points U summary) r j hJ
  constructor
  · apply GeneralPaperRankedInterval.same_lower_position k summary preparedPrefix hMono i j U
    intro a
    have he := projected_test_constant U summary a (hCodes a) r i j hI hJ
    unfold GeneralPaperSignedUpdatePlan.project at he
    by_cases hA : summary.read a<U
    · simp only [hA,ite_true] at he
      exact he
    · omega
  · apply GeneralPaperRankedInterval.same_lower_position k summary preparedPrefix hMono (U+i) (U+j) (2*U)
    intro a
    have he := projected_test_constant U summary a (hCodes a) r i j hI hJ
    unfold GeneralPaperSignedUpdatePlan.project at he
    by_cases hA : summary.read a<U
    · omega
    · simp only [hA,ite_false] at he
      omega

theorem signed_value_constant (k U : ℕ) (summary : Summary k) (preparedPrefix : Prefix k)
    (hMono : Monotone summary.read) (hCodes : ∀ a, summary.read a<2*U)
    (r : Fin (prepare U summary).count) (i j : ℕ)
    (hI : Contains (prepare U summary).intervals r i) (hJ : Contains (prepare U summary).intervals r j) :
    GeneralPaperSignedTailProperties.signedValue k U summary preparedPrefix i=
      GeneralPaperSignedTailProperties.signedValue k U summary preparedPrefix j := by
  have he := tail_counts_constant k U summary preparedPrefix hMono hCodes r i j hI hJ
  unfold GeneralPaperSignedTailProperties.signedValue GeneralPaperSignedTailProperties.tailValue
    GeneralPaperRankedInterval.referenceValue
  simp only [Nat.zero_add,←two_mul]
  rw [he.1,he.2]

end Blotto.GeneralPaperTailCataloguePartition
