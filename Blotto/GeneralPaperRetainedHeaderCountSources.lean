import Blotto.GeneralPaperCountedSamplerInstallation

/-! Concrete source dimensions follow from the actual stored count contract.
Array/list/child counts use the original extracted header shape. The ruler's
fixed-zero count is preserved and its fit follows from its actual owner area.
All source objects here are erased correctness observers, not reader inputs. -/
namespace Blotto.GeneralPaperRetainedHeaderCountSources
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperReferenceRegionSlots GeneralPaperRetainedScalarValue
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperUnifiedFieldValue
open GeneralPaperMixedReferenceMemory (Word)
open GeneralPaperScalarFieldCursor (Cell)
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

theorem scalar_array (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (directory : Directory A)
    (hContract : Contract model A installed directory) (values : List Scalar)
    (hHeader : (GeneralPaperMappedScalarArrayCursor.expected model S A start values).header ∈ directory.headers) :
    (GeneralPaperHeaderCountReadback.count model A installed
      (GeneralPaperMappedScalarArrayCursor.expected model S A start values).header.region.reference).1 = some values.length := by
  have h := (hContract.2.2 _ hHeader (by change (64 : ℕ) ≠ 0; decide)).1
  exact h.trans (congrArg some (GeneralPaperFieldDirectoryLookup.array_target_count model S A start values))

theorem rational_array {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (directory : Directory A)
    (hContract : Contract model A installed directory) (source : FixedArrayTable n ℚ)
    (hHeader : (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.rational)).header ∈ directory.headers) :
    (GeneralPaperHeaderCountReadback.count model A installed
      (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.rational)).header.region.reference).1 = some n := by
  simpa only [List.length_map,Array.length_toList,source.size] using scalar_array model S A start installed directory hContract _ hHeader

theorem natural_array {n : ℕ} (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (directory : Directory A)
    (hContract : Contract model A installed directory) (source : FixedArrayTable n ℕ)
    (hHeader : (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.natural)).header ∈ directory.headers) :
    (GeneralPaperHeaderCountReadback.count model A installed
      (GeneralPaperMappedScalarArrayCursor.expected model S A start (source.data.toList.map Scalar.natural)).header.region.reference).1 = some n := by
  simpa only [List.length_map,Array.length_toList,source.size] using scalar_array model S A start installed directory hContract _ hHeader

def listHeader (model : RationalCostModel) (S A start fixed stride : ℕ) (values : List Scalar) : Header A :=
  let directory := GeneralPaperScalarRecordComponents.listExpected model S A start fixed stride values
  ⟨directory.root,fixed,directory.cells.map (fun cell => cell.region.reference)⟩

theorem list_target_count (model : RationalCostModel) (S A start fixed stride : ℕ) (values : List Scalar) :
    (listHeader model S A start fixed stride values).targets.length = values.length := by
  have h := congrArg List.length (GeneralPaperScalarFieldCursor.cells_values A
    (GeneralPaperSequentialLayout.run model S A (start + A * (stride * values.length + fixed)) (values.map GeneralPaperRetainedScalarValue.encode)).1 values
    (by rw [GeneralPaperSequentialLayout.count,List.length_map]))
  simp only [List.length_map] at h
  change ((GeneralPaperScalarFieldCursor.cells A
    (GeneralPaperSequentialLayout.run model S A (start + A * (stride * values.length + fixed)) (values.map GeneralPaperRetainedScalarValue.encode)).1 values).map
      (fun cell => cell.region.reference)).length = values.length
  rw [List.length_map]
  exact h

theorem scalar_list (model : RationalCostModel) (S A start fixed stride : ℕ) (installed : Installed A) (directory : Directory A)
    (hContract : Contract model A installed directory) (values : List Scalar) (hf : fixed ≠ 0)
    (hHeader : listHeader model S A start fixed stride values ∈ directory.headers) :
    (GeneralPaperHeaderCountReadback.count model A installed (listHeader model S A start fixed stride values).region.reference).1 = some values.length := by
  have h := (hContract.2.2 _ hHeader hf).1
  exact h.trans (congrArg some (list_target_count model S A start fixed stride values))

theorem boolean_width {w : ℕ} (model : RationalCostModel) (S A start : ℕ) (installed : Installed A) (directory : Directory A)
    (hContract : Contract model A installed directory) (source : FixedBinaryWord w)
    (hHeader : listHeader model S A start 32 2 (source.bits.map Scalar.bit) ∈ directory.headers) :
    (GeneralPaperHeaderCountReadback.count model A installed (listHeader model S A start 32 2 (source.bits.map Scalar.bit)).region.reference).1 = some w := by
  simpa only [List.length_map,source.size] using scalar_list model S A start 32 2 installed directory hContract
    (source.bits.map Scalar.bit) (by decide) hHeader

theorem children {α : Type*} (model : RationalCostModel) (A : ℕ) (installed : Installed A) (directory : Directory A)
    (hContract : Contract model A installed directory) (header : Header A) (hHeader : header ∈ directory.headers) (hf : header.fixed ≠ 0)
    (schema : α → List ℕ) (child : α → ℕ → Directory A) (start : ℕ) (values : List α)
    (hTargets : header.targets = (GeneralPaperChildDirectorySpecification.collect
      (GeneralPaperChildDirectorySpecification.directories schema child start values)).roots.map Region.reference) :
    (GeneralPaperHeaderCountReadback.count model A installed header.region.reference).1 = some values.length := by
  have h := (hContract.2.2 header hHeader hf).1
  have hLength : header.targets.length = values.length := by
    rw [hTargets,List.length_map]
    change ((GeneralPaperChildDirectorySpecification.directories schema child start values).map Directory.root).length = values.length
    rw [List.length_map,GeneralPaperChildDirectorySpecification.directory_count]
  exact h.trans (congrArg some hLength)

theorem ruler (model : RationalCostModel) (S A layoutStart rulerStart : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (installed : Installed A) (directory : Directory A) (hContract : Contract model A installed directory)
    (hSafe : GeneralPaperFieldDirectorySafety.Safe (GeneralPaperMeasuredBlockLayout.run model S A layoutStart plan).1 directory)
    (hA : 0 < A) (hCap : layoutStart + plan.sizes.sum < 2 ^ A) (source : List Unit)
    (hHeader : (⟨(GeneralPaperRulerFieldCursor.expected A rulerStart source).root,0,[FixedBinaryWord.ofNat A source.length]⟩ : Header A) ∈ directory.headers) :
    (GeneralPaperHeaderCountReadback.count model A installed (GeneralPaperRulerFieldCursor.expected A rulerStart source).root.reference).1 = some source.length := by
  let header : Header A := ⟨(GeneralPaperRulerFieldCursor.expected A rulerStart source).root,0,[FixedBinaryWord.ofNat A source.length]⟩
  have hBounds := GeneralPaperReferenceLayoutInstallation.capacities model S A layoutStart plan directory.headers hSafe.2.1 hCap header hHeader
  have hFits : source.length < 2 ^ A := by
    have hn : source.length ≤ A * source.length := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right source.length (Nat.succ_le_of_lt hA)
    change rulerStart + A * (2 * source.length + 32) < 2 ^ A at hBounds
    nlinarith
  have h := hContract.2.1.1 header hHeader ⟨0,by change 0 < 1; decide⟩
  change (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory)
    (GeneralPaperRulerFieldCursor.expected A rulerStart source).root.reference 0 0).1 =
      some (⟨A,FixedBinaryWord.ofNat A source.length⟩ : Word) at h
  simp only [GeneralPaperHeaderCountReadback.count,GeneralPaperRulerFieldCursor.read,h,Option.map_some,
    FixedBinaryWord.value_ofNat A source.length hFits]

end Blotto.GeneralPaperRetainedHeaderCountSources
