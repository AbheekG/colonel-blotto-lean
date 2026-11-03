import Blotto.GeneralPaperCellCataloguePrice

/-! Actual partition boundaries supply every cell endpoint cap. The full
partition and optional-entry fill compose without replay; generated summary
and epoch callers supply the original signed-code premises. Padding, catalogue
projection and resource-tag construction remain separate required joins.
-/
namespace Blotto.GeneralPaperActualCellCatalogue
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache
open GeneralPaperCatalogueOptionPlans (signed)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem endpoints_bound {n : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W U : ℕ) (summary : FixedArrayTable n ℕ)
    (r : Fin (GeneralPaperCataloguePartitionPrice.run bits index price W U summary).1.count) :
    (((GeneralPaperCataloguePartitionPrice.run bits index price W U summary).1.intervals).read r).1≤U ∧
    (((GeneralPaperCataloguePartitionPrice.run bits index price W U summary).1.intervals).read r).2≤U := by
  have native (p : GeneralPaperPreparedPartition.Prepared) (hp : p=GeneralPaperTailCataloguePartition.prepare U summary)
      (cell : Fin p.count) : (p.intervals.read cell).1≤U ∧ (p.intervals.read cell).2≤U := by
    subst p
    change Fin (GeneralPaperPreparedPartition.build U (GeneralPaperTailCataloguePartition.points U summary)).count at cell
    change ((GeneralPaperPreparedPartition.build U (GeneralPaperTailCataloguePartition.points U summary)).intervals.read cell).1≤U ∧
      ((GeneralPaperPreparedPartition.build U (GeneralPaperTailCataloguePartition.points U summary)).intervals.read cell).2≤U
    rw [GeneralPaperPreparedPartition.intervals_eq,GeneralPaperBoundaryCells.read_cells]
    exact ⟨GeneralPaperSortedBreakpoints.ordered_bound U _ _ (GeneralPaperPreparedPartition.boundary_member U _ cell.castSucc),
      GeneralPaperSortedBreakpoints.ordered_bound U _ _ (GeneralPaperPreparedPartition.boundary_member U _ cell.succ)⟩
  exact native _ (GeneralPaperCataloguePartitionPrice.data bits index price W U summary) r

theorem partition_and_cells_bit_work {n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summary : FixedArrayTable n ℕ) (hCodes : ∀ r,summary.read r<2*(8*a.C)) :
    let part := GeneralPaperCataloguePartitionPrice.run true (fun w => w) model.rat W (8*a.C) summary
    part.2+(GeneralPaperCellCatalogueExecution.run true (fun w => w) model W a response part.1.intervals).2≤
      GeneralPaperCataloguePartitionPrice.profile model.rat W n (8*a.C)+GeneralPaperCellCataloguePrice.profile model W (n+1) a := by
  let part := GeneralPaperCataloguePartitionPrice.run true (fun w => w) model.rat W (8*a.C) summary
  have hPart := GeneralPaperCataloguePartitionPrice.bit_work model.rat model.monotone W (8*a.C) summary hCodes
  have hCells := GeneralPaperCellCataloguePrice.bit_work model W a response part.1.intervals
    (endpoints_bound true (fun w => w) model.rat W (8*a.C) summary)
  have hCount := GeneralPaperCataloguePartitionPrice.count_bound true (fun w => w) model.rat W (8*a.C) summary
  have hCellsCap := hCells.trans (GeneralPaperCellCataloguePrice.profile_mono model W part.1.count (n+1) a hCount)
  exact Nat.add_le_add hPart hCellsCap

theorem partition_and_cells_arithmetic_work {n : ℕ} (model : RationalCostModel) (a : Alphabet) (response : Bool)
    (summary : FixedArrayTable n ℕ) (hCodes : ∀ r,summary.read r<2*(8*a.C)) :
    let part := GeneralPaperCataloguePartitionPrice.run false (fun _ => 1) (fun _ => 1) 1 (8*a.C) summary
    part.2+(GeneralPaperCellCatalogueExecution.run false (fun _ => 1) model 1 a response part.1.intervals).2≤
      GeneralPaperCataloguePartitionPrice.arithmeticProfile n+GeneralPaperCellCataloguePrice.arithmeticProfile (n+1) a := by
  let part := GeneralPaperCataloguePartitionPrice.run false (fun _ => 1) (fun _ => 1) 1 (8*a.C) summary
  have hPart := GeneralPaperCataloguePartitionPrice.arithmetic_work (8*a.C) summary hCodes
  have hCells := GeneralPaperCellCataloguePrice.arithmetic_work model a response part.1.intervals
  have hCount := GeneralPaperCataloguePartitionPrice.count_bound false (fun _ => 1) (fun _ => 1) 1 (8*a.C) summary
  have hCellsCap := hCells.trans (GeneralPaperCellCataloguePrice.arithmetic_profile_mono part.1.count (n+1) a hCount)
  exact Nat.add_le_add hPart hCellsCap

theorem generated_work (model : RationalCostModel) (W m k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (digits : ℕ) (trees : Trees m a.lambda) (hValid : Valid a k trees) (hPaths : Paths a k trees)
    (arrays : GeneralPaperFourSummaryArrays.Arrays m k)
    (hArrays : arrays=(GeneralPaperFourSummaryArrays.run true (fun w => w) model.rat W m k Qv a c hc digits trees).1)
    (response : Bool) (field : Fin m) :
    let summary := (signed response arrays).read field
    let part := GeneralPaperCataloguePartitionPrice.run true (fun w => w) model.rat W (8*a.C) summary
    part.2+(GeneralPaperCellCatalogueExecution.run true (fun w => w) model W a response part.1.intervals).2≤
      GeneralPaperCataloguePartitionPrice.profile model.rat W (GeneralPaperSourceParameters.prepare k).summarySize (8*a.C)+
        GeneralPaperCellCataloguePrice.profile model W ((GeneralPaperSourceParameters.prepare k).summarySize+1) a :=
  partition_and_cells_bit_work model W a response ((signed response arrays).read field)
    (GeneralPaperActualCataloguePartition.generated_codes true (fun w => w) model.rat W m k Qv a c hc digits trees hValid hPaths arrays hArrays response field)

theorem epoch_work {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (he : epoch≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (response : Bool) (field : Fin m) :
    let trees := GeneralPaperCatalogueOuterLoop.treesAt (GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br) a k epoch
    let arrays := (GeneralPaperFourSummaryArrays.run true (fun w => w) model.rat W m k Qv a c hc
      (GeneralPaperQuantileComparison.width a.lambda k) trees).1
    let summary := (signed response arrays).read field
    let part := GeneralPaperCataloguePartitionPrice.run true (fun w => w) model.rat W (8*a.C) summary
    part.2+(GeneralPaperCellCatalogueExecution.run true (fun w => w) model W a response part.1.intervals).2≤
      GeneralPaperCataloguePartitionPrice.profile model.rat W (GeneralPaperSourceParameters.prepare k).summarySize (8*a.C)+
        GeneralPaperCellCataloguePrice.profile model W ((GeneralPaperSourceParameters.prepare k).summarySize+1) a :=
  generated_work model W m k Qv a c hc _ _
    (GeneralPaperCatalogueOuterValidity.trees_valid a k Qv weights Bc Br epoch he)
    (GeneralPaperCatalogueOuterValidity.trees_paths a k Qv weights Bc Br epoch he) _ rfl response field

end Blotto.GeneralPaperActualCellCatalogue
