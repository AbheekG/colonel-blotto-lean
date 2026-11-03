import Blotto.GeneralPaperFieldDirectoryPartition

/-! Complete owner partitions derive cross header/scalar interval separation,
not merely separate ordering. Raw header keys and scalar roots are disjoint,
and their joint modeled encoded area fits the actual measured extent. -/
namespace Blotto.GeneralPaperFieldDirectorySeparation
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperReferenceRegionSlots
open GeneralPaperFieldDirectorySafety GeneralPaperFieldDirectoryPartition GeneralPaperRetainedScalarValue
open GeneralPaperScalarFieldCursor (Cell)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

theorem cross_regions (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory) :
    ∀ header ∈ directory.headers,∀ cell ∈ directory.cells,
      Disjoint (Set.Ico header.region.start header.region.stop) (Set.Ico cell.region.start cell.region.stop) := by
  have hLayout := GeneralPaperMeasuredBlockLayout.disjoint model S A start plan
  have hOwners := hCovered.symm.pairwise hLayout (by intro x y h; exact h.symm)
  have hCross := (List.pairwise_append.mp hOwners).2.2
  intro header hh cell hc
  exact hCross header.region (List.mem_map.mpr ⟨header,hh,rfl⟩) cell.region (List.mem_map.mpr ⟨cell,hc,rfl⟩)

theorem cross_keys (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    List.Disjoint ((GeneralPaperReferenceRegionProgram.collect model S A directory.headers).entries.map (fun entry => entry.location.value))
      (directory.cells.map (fun cell => cell.region.reference.value)) := by
  have hFrom : GeneralPaperReferenceLayoutInstallation.FromLayout model S A start plan directory.headers := hSafe.2.1
  have hCaps := GeneralPaperReferenceLayoutInstallation.capacities model S A start plan directory.headers hFrom hCap
  apply List.disjoint_left.mpr
  intro key hWord hScalar
  obtain ⟨entry,he,hEntryKey⟩ := List.mem_map.mp hWord
  obtain ⟨cell,hc,hCellKey⟩ := List.mem_map.mp hScalar
  obtain ⟨header,hh,hBatch⟩ := (GeneralPaperReferenceRegionProgram.member model S A directory.headers entry).mp he
  have hHeaderKey := GeneralPaperReferenceRegionSlots.entry_key_in_region model S A header hA (hSafe.2.2.2.1 header hh)
    (hCaps header hh) entry hBatch
  have hCellRegion : cell.region ∈ (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 :=
    hSafe.2.2.1.subset (List.mem_map.mpr ⟨cell,hc,rfl⟩)
  have hCellReference := GeneralPaperMeasuredBlockLayout.references model S A start plan hCap cell.region hCellRegion
  have hCellPositive : 0 < cell.region.length := by rw [hSafe.2.2.2.2 cell hc]; exact positive cell.value
  have hCellRoot : cell.region.reference.value ∈ Set.Ico cell.region.start cell.region.stop := by
    rw [hCellReference]
    exact ⟨le_refl _,by unfold Region.stop; omega⟩
  rw [hEntryKey] at hHeaderKey
  rw [hCellKey] at hCellRoot
  exact Set.disjoint_left.mp (cross_regions model S A start plan directory hCovered header hh cell hc) hHeaderKey hCellRoot

theorem owner_area (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory) :
    (directory.headers.map (fun header => header.region.length)).sum +
      (directory.cells.map (fun cell => cell.region.length)).sum = plan.sizes.sum := by
  have h := (hCovered.map Region.length).sum_eq
  rw [List.map_append,List.sum_append,GeneralPaperMeasuredBlockLayout.lengths] at h
  simpa only [List.map_map,Function.comp_def] using h

theorem joint_area (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory) :
    A * GeneralPaperReferenceHeaderSlotArea.slots directory.headers +
      (directory.cells.map (fun cell => encode cell.value)).sum ≤ plan.sizes.sum := by
  have hHeaders := GeneralPaperReferenceHeaderSlotArea.owner_area A directory.headers hSafe.2.2.2.1
  have hArea := owner_area model S A start plan directory hCovered
  have hEq : directory.cells.map (fun cell => encode cell.value) = directory.cells.map (fun cell => cell.region.length) :=
    List.map_congr_left (fun cell hc => (hSafe.2.2.2.2 cell hc).symm)
  rw [hEq]
  omega

theorem matrix_cross_regions {m r : ℕ} (model : RationalCostModel) (S A start : ℕ)
    (source : FixedArrayTable r (FixedArrayTable m ℚ)) :
    ∀ header ∈ (GeneralPaperMatrixFieldCursor.expected model S A start source).headers,
      ∀ cell ∈ (GeneralPaperMatrixFieldCursor.expected model S A start source).cells,
        Disjoint (Set.Ico header.region.start header.region.stop) (Set.Ico cell.region.start cell.region.stop) :=
  cross_regions model S A start (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source)
    (GeneralPaperMatrixFieldCursor.expected model S A start source) (GeneralPaperFieldDirectoryPartition.matrix model S A start source)

theorem matrix_joint_area {m r : ℕ} (model : RationalCostModel) (S A start : ℕ)
    (source : FixedArrayTable r (FixedArrayTable m ℚ)) :
    A * GeneralPaperReferenceHeaderSlotArea.slots (GeneralPaperMatrixFieldCursor.expected model S A start source).headers +
      ((GeneralPaperMatrixFieldCursor.expected model S A start source).cells.map (fun cell => encode cell.value)).sum ≤
        (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source).sizes.sum :=
  joint_area model S A start (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source)
    (GeneralPaperMatrixFieldCursor.expected model S A start source)
    (GeneralPaperMatrixFieldCursor.success model S A start source []).2.2 (GeneralPaperFieldDirectoryPartition.matrix model S A start source)

end Blotto.GeneralPaperFieldDirectorySeparation
