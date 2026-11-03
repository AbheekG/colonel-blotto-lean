import Blotto.GeneralPaperDirectoryPrependLifetime

/-! One complete child-loop output body has additive measured ownership.
Root count is explicit, since abstract safe bodies may repeat roots. Header
and scalar-cell lists retain actual sublist ownership and payload widths. -/
namespace Blotto.GeneralPaperDirectoryBodyStorage
open GeneralPaperFieldDirectory (Body)
open GeneralPaperFieldDirectorySafety (SafeBody)
open GeneralPaperMeasuredBlockPlan (Plan)
open GeneralPaperScalarFieldCursor (Cell)
open GeneralPaperReferenceRegionSlots (Header)
open GeneralPaperSequentialLayout (Region)
open GeneralPaperRetainedScalarValue (encode)
open GeneralPaperEncodedScalarStorage
open GeneralPaperDirectoryPrependLifetime (bodyFoot)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def bound (S A B N : ℕ) : ℕ := (B + N + 1) * 4096 * (S + A + 1)

theorem body_bound (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (body : Body A)
    (hSafe : SafeBody (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 body)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A)
    (hCap : start + plan.sizes.sum < 2 ^ A) : bodyFoot S body ≤ bound S A plan.sizes.sum body.roots.length := by
  have hRange := GeneralPaperMeasuredBlockLayout.range model S A start plan
  have hRegions : ∀ region ∈ (GeneralPaperMeasuredBlockLayout.run model S A start plan).1,
      GeneralPaperMeasuredLayoutStorage.regionFoot S region ≤ GeneralPaperMeasuredLayoutStorage.regionBound S A := by
    intro region hr
    exact GeneralPaperMeasuredLayoutStorage.region_bound S A region hA ((hRange region hr).2.trans_lt hCap)
  have hRoots := list_bound S (GeneralPaperMeasuredLayoutStorage.regionBound S A)
    (GeneralPaperMeasuredLayoutStorage.regionFoot S) body.roots (fun r hr => hRegions r (hSafe.1 r hr))
  have hCaps := GeneralPaperReferenceLayoutInstallation.capacities model S A start plan body.headers hSafe.2.1 hCap
  have hHeaders := GeneralPaperFieldDirectoryStorage.headers_bound S A body.headers hA hSafe.2.2.2.1 hCaps
  have hCells := GeneralPaperFieldDirectoryStorage.cells_bound S A body.cells (fun cell hc =>
    hRegions cell.region (hSafe.2.2.1.subset (List.mem_map.mpr ⟨cell,hc,rfl⟩)))
  have hHeaderCount := hSafe.2.1.length_le
  have hCellCount := hSafe.2.2.1.length_le
  rw [List.length_map,GeneralPaperMeasuredBlockLayout.count] at hHeaderCount hCellCount
  have hBlocks := GeneralPaperMeasuredPlanPositive.block_count plan hPos
  have hSlots := GeneralPaperReferenceHeaderSlotArea.layout_count model S A start plan body.headers hSafe.2.1 hA hSafe.2.2.2.1
  have hArea := GeneralPaperReferenceHeaderSlotArea.sum_sublist _ _ (hSafe.2.2.1.map Region.length)
  rw [GeneralPaperMeasuredBlockLayout.lengths] at hArea
  simp only [List.map_map,Function.comp_def] at hArea
  have hLengths : body.cells.map (fun cell => cell.region.length) = body.cells.map (fun cell => encode cell.value) :=
    List.map_congr_left (fun cell hc => hSafe.2.2.2.2 cell hc)
  rw [hLengths] at hArea
  have hH := Nat.mul_le_mul_right (384 * (S + A + 1))
    (show GeneralPaperReferenceHeaderSlotArea.slots body.headers + body.headers.length ≤ 2 * plan.sizes.sum by omega)
  have hC := Nat.mul_le_mul_right (192 * (S + A + 1)) (hCellCount.trans hBlocks)
  have hLinks := Nat.mul_le_mul_right (2 * S) (show body.headers.length + body.cells.length ≤ 2 * plan.sizes.sum by omega)
  have hPayload := Nat.mul_le_mul_left plan.sizes.sum (show 1 ≤ S + A + 1 by omega)
  unfold bodyFoot GeneralPaperMeasuredLayoutStorage.regionsFoot
  change _ + ((body.headers.map (GeneralPaperFieldDirectoryStorage.headerFoot S)).sum + body.headers.length * (2 * S) + 32 * S) +
    ((body.cells.map (GeneralPaperFieldDirectoryStorage.cellFoot S)).sum + body.cells.length * (2 * S) + 32 * S) + 64 * S ≤ _
  unfold bound GeneralPaperMeasuredLayoutStorage.regionBound at *
  nlinarith only [hRoots,hHeaders,hCells,hH,hC,hLinks,hArea,hPayload]

end Blotto.GeneralPaperDirectoryBodyStorage
