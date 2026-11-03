import Blotto.GeneralPaperMeasuredPlanWorkRates

/-! Complete temporary-directory copying work. Actual valid region owners
bound address metadata and target counts. Scalar cells retain an additive
sum of payload widths. Appending a child traverses only that child once. -/
namespace Blotto.GeneralPaperDirectoryCopyWork
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperReferenceRegionSlots
open GeneralPaperFieldDirectorySafety GeneralPaperMeasuredPlanWorkAlgebra
open GeneralPaperScalarFieldCursor (Cell)
open GeneralPaperRetainedScalarValue (encode)
open GeneralPaperEncodedScalarStorage (natBits)
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem metadata (model : RationalCostModel) (S A : ℕ) :
    1 ≤ unit model S A ∧ 128 * (S + A + 1) ≤ unit model S A ∧
      A + 32 * (S + S + 1) + 64 * (S + S + 1) ≤ unit model S A := by
  unfold unit
  omega

theorem region_work (model : RationalCostModel) (S A : ℕ) (region : Region A)
    (hA : 0 < A) (hCap : region.stop < 2 ^ A) :
    GeneralPaperLastRegionSelection.price S A region ≤ unit model S A := by
  have hStart := binaryWordWidth_le_of_lt_pow hA (show region.start < 2 ^ A by unfold Region.stop at hCap; omega)
  have hLength := binaryWordWidth_le_of_lt_pow hA (show region.length < 2 ^ A by unfold Region.stop at hCap; omega)
  unfold GeneralPaperLastRegionSelection.price natBits unit
  omega

theorem layout_region_work (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    ∀ region ∈ (GeneralPaperMeasuredBlockLayout.run model S A start plan).1,
      GeneralPaperLastRegionSelection.price S A region ≤ unit model S A := by
  intro region hr
  have h := GeneralPaperMeasuredBlockLayout.range model S A start plan region hr
  exact region_work model S A region hA (h.2.trans_lt hCap)

theorem header_work (model : RationalCostModel) (S A : ℕ) (header : Header A)
    (hA : 0 < A) (hValid : Valid header) (hCap : header.region.stop < 2 ^ A) :
    (copyHeader S A header).2 ≤ (header.targets.length + 1) * 3 * unit model S A := by
  have hCopy := GeneralPaperReferenceCopy.list_bound S S (A + 32 * (S + S + 1))
    (GeneralPaperReferenceCopy.scalar S S (fun _ : FixedBinaryWord A => A)) header.targets (fun _ _ => le_rfl)
  have hRegion := region_work model S A header.region hA hCap
  obtain ⟨_,_,hFixed,_⟩ := GeneralPaperStoredHeaderPreparationWork.owner_widths header hA hValid hCap
  have hMeta := metadata model S A
  have hm := Nat.mul_le_mul_left (header.targets.length + 1) hMeta.2.2
  have hRest : natBits header.fixed + 64 * (S + A + 1) ≤ unit model S A := by unfold natBits unit; omega
  change (GeneralPaperReferenceCopy.list S S (GeneralPaperReferenceCopy.scalar S S (fun _ : FixedBinaryWord A => A)) header.targets).2 +
    GeneralPaperLastRegionSelection.price S A header.region + natBits header.fixed + 64 * (S + A + 1) ≤ _
  nlinarith only [hCopy,hRegion,hm,hRest,Nat.zero_le (header.targets.length * unit model S A)]

theorem headers_work (model : RationalCostModel) (S A : ℕ) (headers rest : List (Header A))
    (hA : 0 < A) (hValid : ∀ h ∈ headers,Valid h) (hCap : ∀ h ∈ headers,h.region.stop < 2 ^ A) :
    (appendHeaders S A headers rest).2 ≤
      (GeneralPaperReferenceHeaderSlotArea.slots headers + headers.length + 1) * 4 * unit model S A := by
  induction headers with
  | nil =>
    change 64 * (S + A + 1) ≤ (0 + 0 + 1) * 4 * unit model S A
    have h := metadata model S A
    omega
  | cons header headers ih =>
    have hh : header ∈ header :: headers := List.mem_cons_self ..
    have hp := header_work model S A header hA (hValid header hh) (hCap header hh)
    have ht := ih (fun h hm => hValid h (List.mem_cons_of_mem _ hm)) (fun h hm => hCap h (List.mem_cons_of_mem _ hm))
    have hMeta := metadata model S A
    change (copyHeader S A header).2 + (appendHeaders S A headers rest).2 + 64 * (S + A + 1) ≤ _
    simp only [GeneralPaperReferenceHeaderSlotArea.slots,List.map_cons,List.sum_cons,List.length_cons] at ht ⊢
    nlinarith only [hp,ht,hMeta.2.1,Nat.zero_le (header.targets.length * unit model S A)]

theorem cells_work (model : RationalCostModel) (S A : ℕ) (cells rest : List (Cell A))
    (hRegion : ∀ cell ∈ cells,GeneralPaperLastRegionSelection.price S A cell.region ≤ unit model S A) :
    (appendCells S A cells rest).2 ≤ (cells.map (fun cell => encode cell.value)).sum +
      (2 * cells.length + 1) * unit model S A := by
  induction cells with
  | nil =>
    change 64 * (S + A + 1) ≤ 0 + (2 * 0 + 1) * unit model S A
    have h := metadata model S A
    omega
  | cons cell cells ih =>
    have hh := hRegion cell (List.mem_cons_self ..)
    have ht := ih (fun c hc => hRegion c (List.mem_cons_of_mem _ hc))
    have hMeta := metadata model S A
    change (appendCells S A cells rest).2 + GeneralPaperLastRegionSelection.price S A cell.region + encode cell.value + 64 * (S + A + 1) ≤ _
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith only [hh,ht,hMeta.2.1]

theorem headers_layout_work (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (headers rest : List (Header A))
    (hFrom : (headers.map Header.region).Sublist (GeneralPaperMeasuredBlockLayout.run model S A start plan).1)
    (hValid : ∀ h ∈ headers,Valid h) (hPos : GeneralPaperMeasuredPlanPositive.Positive plan)
    (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    (appendHeaders S A headers rest).2 ≤ (plan.sizes.sum + 1) * 8 * unit model S A := by
  have hCaps := GeneralPaperReferenceLayoutInstallation.capacities model S A start plan headers hFrom hCap
  have h := headers_work model S A headers rest hA hValid hCaps
  have hSlots := GeneralPaperReferenceHeaderSlotArea.layout_count model S A start plan headers hFrom hA hValid
  have hCount := hFrom.length_le
  rw [List.length_map,GeneralPaperMeasuredBlockLayout.count] at hCount
  have hBlocks := GeneralPaperMeasuredPlanPositive.block_count plan hPos
  have hm := Nat.mul_le_mul_right (4 * unit model S A)
    (show GeneralPaperReferenceHeaderSlotArea.slots headers + headers.length + 1 ≤ 2 * (plan.sizes.sum + 1) by omega)
  nlinarith only [h,hm]

theorem payload_area (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory) :
    (directory.cells.map (fun cell => encode cell.value)).sum ≤ plan.sizes.sum := by
  have h := GeneralPaperReferenceHeaderSlotArea.sum_sublist _ _ (hSafe.2.2.1.map Region.length)
  rw [GeneralPaperMeasuredBlockLayout.lengths] at h
  simp only [List.map_map,Function.comp_def] at h
  have he : directory.cells.map (fun cell => cell.region.length) = directory.cells.map (fun cell => encode cell.value) :=
    List.map_congr_left (fun cell hc => hSafe.2.2.2.2 cell hc)
  rw [he] at h
  exact h

theorem prepend_work (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (tail : Body A)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    (prepend S A directory tail).2 ≤ (plan.sizes.sum + 1) * 16 * unit model S A := by
  have hHeaders := headers_layout_work model S A start plan directory.headers tail.headers hSafe.2.1 hSafe.2.2.2.1 hPos hA hCap
  have hRegions := layout_region_work model S A start plan hA hCap
  have hCells := cells_work model S A directory.cells tail.cells (fun cell hc => hRegions cell.region
    (hSafe.2.2.1.subset (List.mem_map.mpr ⟨cell,hc,rfl⟩)))
  have hRoot := hRegions directory.root hSafe.1
  have hArea := payload_area model S A start plan directory hSafe
  have hCounts := GeneralPaperStoredDirectoryPreparationWork.directory_counts model S A start plan directory hSafe hPos
  have hMeta := metadata model S A
  have hPay : (directory.cells.map (fun cell => encode cell.value)).sum ≤ plan.sizes.sum * unit model S A :=
    hArea.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left plan.sizes.sum hMeta.1)
  have hm := Nat.mul_le_mul_right (unit model S A) (show 2 * directory.cells.length + 1 ≤ 2 * plan.sizes.sum + 1 by omega)
  change (appendHeaders S A directory.headers tail.headers).2 + (appendCells S A directory.cells tail.cells).2 +
    GeneralPaperLastRegionSelection.price S A directory.root + 64 * (S + A + 1) ≤ _
  nlinarith only [hHeaders,hCells,hRoot,hPay,hm,hMeta.2.1,Nat.zero_le (plan.sizes.sum * unit model S A)]

end Blotto.GeneralPaperDirectoryCopyWork
