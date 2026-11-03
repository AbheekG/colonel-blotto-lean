import Blotto.GeneralPaperPayloadMemoryOwnership

/-! Both actual installation passes own one RAM. Their resident payload
reserve adds incoming memory, reference words and a single scalar-width
sum. Actual safe/covered layouts bound that sum by measured extent, also
after count expansion and during same-memory outer attachment. -/
namespace Blotto.GeneralPaperUnifiedInstallationOwnership
open GeneralPaperPayloadMemoryOwnership (Bounded payload)
open GeneralPaperUnifiedFieldValue (Value Memory encode)
open GeneralPaperUnifiedFieldMemory
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperFieldDirectorySafety (Safe)
open GeneralPaperFieldDirectoryPartition (Covered)
open GeneralPaperMeasuredBlockPlan (Plan)
open GeneralPaperScalarFieldCursor (Cell)
open GeneralPaperUnifiedDirectoryInstallation (Installed)
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

theorem word_prefix (S A B : ℕ) (words : List (GeneralPaperReferenceSlotConstruction.Entry A))
    (memory : Memory) (hMemory : Bounded encode memory B) (depth : ℕ) :
    Bounded encode
      (GeneralPaperPayloadMemory.install S A encode memory ((liftWords S A words).1.take depth)).1
      (B + words.length * A) := by
  have h := GeneralPaperPayloadMemoryOwnership.prefix_bounded S A encode memory B hMemory (liftWords S A words).1 depth
  simpa only [payload,word_payload] using h

theorem scalar_prefix (S A B : ℕ) (words : List (GeneralPaperReferenceSlotConstruction.Entry A))
    (scalars : List (GeneralPaperPayloadMemory.Entry A GeneralPaperRetainedScalarValue.Scalar))
    (memory : Memory) (hMemory : Bounded encode memory B) (depth : ℕ) :
    Bounded encode
      (GeneralPaperPayloadMemory.install S A encode
        (GeneralPaperPayloadMemory.install S A encode memory (liftWords S A words).1).1
        ((liftScalars S A scalars).1.take depth)).1
      (B + words.length * A + (scalars.map (fun entry => GeneralPaperRetainedScalarValue.encode entry.2)).sum) := by
  have hFirst := GeneralPaperPayloadMemoryOwnership.install_bounded S A encode memory B hMemory (liftWords S A words).1
  have hSecond := GeneralPaperPayloadMemoryOwnership.prefix_bounded S A encode _ _ hFirst (liftScalars S A scalars).1 depth
  simpa only [payload,word_payload,scalar_payload] using hSecond

theorem prepare_bounded (S A B : ℕ) (words : List (GeneralPaperReferenceSlotConstruction.Entry A))
    (scalars : List (GeneralPaperPayloadMemory.Entry A GeneralPaperRetainedScalarValue.Scalar))
    (memory : Memory) (hMemory : Bounded encode memory B) :
    Bounded encode (prepare S A words scalars memory).1
      (B + words.length * A + (scalars.map (fun entry => GeneralPaperRetainedScalarValue.encode entry.2)).sum) := by
  have hFirst := GeneralPaperPayloadMemoryOwnership.install_bounded S A encode memory B hMemory (liftWords S A words).1
  have hSecond := GeneralPaperPayloadMemoryOwnership.install_bounded S A encode _ _ hFirst (liftScalars S A scalars).1
  simpa only [prepare,payload,word_payload,scalar_payload] using hSecond

theorem directory_install (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (directory : Directory A)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory) :
    Bounded encode (GeneralPaperUnifiedDirectoryInstallation.install model S A directory).memory plan.sizes.sum := by
  have h := prepare_bounded S A 0 (GeneralPaperReferenceRegionProgram.collect model S A directory.headers).entries
    (directory.cells.map Cell.entry) (GeneralPaperPayloadMemory.empty Value)
    (GeneralPaperPayloadMemoryOwnership.empty_bounded encode)
  have hInstalled : Bounded encode (GeneralPaperUnifiedDirectoryInstallation.install model S A directory).memory
      (GeneralPaperReferenceHeaderSlotArea.slots directory.headers * A +
        (directory.cells.map (fun cell => GeneralPaperRetainedScalarValue.encode cell.value)).sum) := by
    simpa only [GeneralPaperUnifiedDirectoryInstallation.install,GeneralPaperReferenceRegionProgram.count,GeneralPaperReferenceHeaderSlotArea.slots,
      List.map_map,Cell.entry,Function.comp_def,Nat.zero_add] using h
  have hArea := GeneralPaperFieldDirectorySeparation.joint_area model S A start plan directory hSafe hCovered
  exact GeneralPaperPayloadMemoryOwnership.mono encode _ _ _ hInstalled (by nlinarith only [hArea])

theorem directory_extension (model : RationalCostModel) (S A start B : ℕ) (plan : Plan) (directory : Directory A)
    (memory : Memory) (hMemory : Bounded encode memory B)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory) :
    Bounded encode (GeneralPaperStoredDirectoryExtension.install model S A directory memory).memory (B + plan.sizes.sum) := by
  have h := prepare_bounded S A B (GeneralPaperReferenceRegionProgram.collect model S A directory.headers).entries
    (directory.cells.map Cell.entry) memory hMemory
  have hInstalled : Bounded encode (GeneralPaperStoredDirectoryExtension.install model S A directory memory).memory
      (B + GeneralPaperReferenceHeaderSlotArea.slots directory.headers * A +
        (directory.cells.map (fun cell => GeneralPaperRetainedScalarValue.encode cell.value)).sum) := by
    simpa only [GeneralPaperStoredDirectoryExtension.install,GeneralPaperReferenceRegionProgram.count,GeneralPaperReferenceHeaderSlotArea.slots,
      List.map_map,Cell.entry,Function.comp_def] using h
  have hArea := GeneralPaperFieldDirectorySeparation.joint_area model S A start plan directory hSafe hCovered
  exact GeneralPaperPayloadMemoryOwnership.mono encode _ _ _ hInstalled (by nlinarith only [hArea])

theorem counted_install (model : RationalCostModel) (S A start prefixWork : ℕ) (plan : Plan) (directory : Directory A)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory) :
    Bounded encode (GeneralPaperHeaderCountInstallation.finish model S A prefixWork directory).memory plan.sizes.sum := by
  have h := directory_install model S A start plan (GeneralPaperHeaderCountDirectory.expanded directory)
    (GeneralPaperHeaderCountDirectory.safe _ directory hSafe) (GeneralPaperHeaderCountDirectory.covered _ directory hCovered)
  simpa only [GeneralPaperHeaderCountInstallation.finish,GeneralPaperHeaderCountDirectory.data] using h

theorem outer_attachment (model : RationalCostModel) (S I A start B prefixWork : ℕ)
    (inner : Installed I) (hInner : Bounded encode inner.memory B) (tag : ℕ) :
    Bounded encode (GeneralPaperStoredOuterAttachment.finish model S I A prefixWork
      (GeneralPaperEqualOuterFieldLayout.canonical A start) inner tag).memory
      (B + (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum) := by
  exact directory_extension model S A start B (GeneralPaperEqualMeasuredSelectedPlan.header model S A)
    (GeneralPaperStoredOuterDirectory.directory A (GeneralPaperEqualOuterFieldLayout.canonical A start)
      (GeneralPaperStoredWordEncoding.word model S A inner.root.value).1 (GeneralPaperStoredWordEncoding.word model S A tag).1)
    inner.memory hInner (GeneralPaperStoredOuterDirectory.safe model S A start _ _)
    (GeneralPaperStoredOuterDirectory.covered model S A start _ _)

end Blotto.GeneralPaperUnifiedInstallationOwnership
