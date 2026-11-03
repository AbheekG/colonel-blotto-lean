import Blotto.GeneralPaperMeasuredUnequalFullContract

/-! Changing only the initializer charge preserves every selected/copied
payload and installed memory. Actual saved work fields decrease. -/
namespace Blotto.GeneralPaperMeasuredEqualRepricing
open GeneralPaperEqualInputDomain
open GeneralPaperUnifiedFieldValue (Memory Value)
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

theorem selected_data (model : RationalCostModel) (A B K : ℕ) (p : Input model) :
    (GeneralPaperEqualSelectedPipeline.run model A K p).1 =
      (GeneralPaperEqualSelectedPipeline.run model B K p).1 := by
  rw [GeneralPaperEqualSelectedPipeline.data, GeneralPaperEqualSelectedPipeline.data]

theorem copied_data (model : RationalCostModel) (A B K : ℕ) (p : Input model) :
    (GeneralPaperEqualCopiedPipeline.run model A K p).1 =
      (GeneralPaperEqualCopiedPipeline.run model B K p).1 := by
  rw [GeneralPaperEqualCopiedPipeline.data, GeneralPaperEqualCopiedPipeline.data]

theorem selected_work (model : RationalCostModel) (A B K : ℕ) (h : A ≤ B) (p : Input model) :
    (GeneralPaperEqualSelectedPipeline.run model A K p).2 ≤
      (GeneralPaperEqualSelectedPipeline.run model B K p).2 := by
  rw [GeneralPaperEqualSelectedPipeline.work, GeneralPaperEqualSelectedPipeline.work]
  exact Nat.add_le_add_right (GeneralPaperMeasuredInitializerMonotonicity.initialization model A B K h p) _

def controls (model : RationalCostModel) (A K : ℕ) (p : Input model) : List ℕ :=
  let S := word K p
  let source := GeneralPaperEqualCopiedPipeline.run model A K p
  let built := GeneralPaperStoredSelectedConstruction.run model S source.1
  [S, K, p.n, p.k, source.1.address, (GeneralPaperEqualSelectedPipeline.run model A K p).2,
    source.2, built.2, source.2 + built.2, (GeneralPaperStoredSelectedPipeline.run model A K p).2]

theorem controls_mono (model : RationalCostModel) (A B K : ℕ) (h : A ≤ B) (p : Input model) :
    List.Forall₂ (fun x y => x ≤ y) (controls model A K p) (controls model B K p) := by
  have hs := selected_work model A B K h p
  have hc := GeneralPaperMeasuredEqualWork.copied_mono model A B K h p
  have hp := GeneralPaperMeasuredEqualWork.pipeline_mono model A B K h p
  have hd := copied_data model A B K p
  dsimp only [controls]
  rw [hd]
  simp [List.forall₂_cons, hs, hc, hp]

def memory (model : RationalCostModel) (A K : ℕ) (p : Input model) : Memory :=
  (GeneralPaperStoredSelectedPipeline.run model A K p).1.elim
    (GeneralPaperPayloadMemory.empty Value) (fun output => output.memory)

theorem memory_construction (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    memory model A K p =
      (GeneralPaperStoredSelectedConstruction.run model (word K p) (GeneralPaperEqualCopiedPipeline.run model A K p).1).1.elim
        (GeneralPaperPayloadMemory.empty Value) (fun output => output.memory) := by
  dsimp only [memory, GeneralPaperStoredSelectedPipeline.run, GeneralPaperStoredSelectedPipeline.width]
  split <;> simp_all [GeneralPaperSamplerRecordInstallation.attach]

theorem memory_reprice (model : RationalCostModel) (A B K : ℕ) (p : Input model) :
    memory model A K p = memory model B K p := by
  rw [memory_construction, memory_construction, copied_data model A B K p]

theorem attachment_mono {A : ℕ} (S a b : ℕ) (h : a ≤ b)
    (output : GeneralPaperUnifiedDirectoryInstallation.Installed A) :
    GeneralPaperResultAttachmentLifetime.window S A a output ≤
      GeneralPaperResultAttachmentLifetime.window S A b output := by
  have hf := GeneralPaperMixedPrimitiveStorage.fields_mono S
    (GeneralPaperResultAttachmentLifetime.controls S A a output)
    (GeneralPaperResultAttachmentLifetime.controls S A b output) (by
      dsimp only [GeneralPaperResultAttachmentLifetime.controls, GeneralPaperSamplerRecordInstallation.attach]
      simp [List.forall₂_cons, h])
  unfold GeneralPaperResultAttachmentLifetime.window
  omega

end Blotto.GeneralPaperMeasuredEqualRepricing
