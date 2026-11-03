import Blotto.GeneralPaperHeaderCountReadback

/-! Count preparation precedes the one directory installation. Actual layout
ownership derives count representability. The same installed memory preserves
every earlier readback and exposes each positive-prefix header's count. -/
namespace Blotto.GeneralPaperHeaderCountInstallation
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperReferenceRegionSlots
open GeneralPaperFieldDirectorySafety GeneralPaperFieldDirectoryPartition
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 8192

def finish (model : RationalCostModel) (S A prefixWork : ℕ) (directory : Directory A) : Installed A :=
  let counted := GeneralPaperHeaderCountDirectory.prepare model S A directory
  let actual := GeneralPaperUnifiedDirectoryInstallation.install model S A counted.1
  ⟨actual.memory,actual.root,prefixWork + counted.2 + actual.work + 128 * (S + A + 1)⟩

def Contract (model : RationalCostModel) (A : ℕ) (output : Installed A) (directory : Directory A) : Prop :=
  Readback model A output (GeneralPaperHeaderCountDirectory.expanded directory) ∧ Readback model A output directory ∧
  ∀ header ∈ directory.headers,header.fixed ≠ 0 →
    (GeneralPaperHeaderCountReadback.count model A output header.region.reference).1 = some header.targets.length ∧
    (GeneralPaperHeaderCountReadback.count model A output header.region.reference).2 =
      (GeneralPaperMixedReferenceRegionProgram.read model A (GeneralPaperUnifiedFieldValue.referenceMemory output.memory)
        header.region.reference 0 0).2 + 65 * A + 64

theorem root (model : RationalCostModel) (S A prefixWork : ℕ) (directory : Directory A) :
    (finish model S A prefixWork directory).root = directory.root.reference := by
  simp only [finish,GeneralPaperHeaderCountDirectory.data,GeneralPaperHeaderCountDirectory.expanded,
    GeneralPaperUnifiedDirectoryInstallation.install]

theorem work (model : RationalCostModel) (S A prefixWork : ℕ) (directory : Directory A) :
    (finish model S A prefixWork directory).work = prefixWork + (GeneralPaperHeaderCountDirectory.prepare model S A directory).2 +
      (GeneralPaperUnifiedDirectoryInstallation.install model S A (GeneralPaperHeaderCountDirectory.expanded directory)).work +
      128 * (S + A + 1) := by
  simp only [finish,GeneralPaperHeaderCountDirectory.data]

theorem contract (model : RationalCostModel) (S A start prefixWork : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    Contract model A (finish model S A prefixWork directory) directory := by
  have hNew : Readback model A (finish model S A prefixWork directory) (GeneralPaperHeaderCountDirectory.expanded directory) := by
    have h := GeneralPaperSamplerRecordInstallation.installation_readback model S A start plan
      (GeneralPaperHeaderCountDirectory.expanded directory) (GeneralPaperHeaderCountDirectory.safe _ directory hSafe)
      (GeneralPaperHeaderCountDirectory.covered _ directory hCovered) hPos hA hCap
    dsimp only [finish]
    rw [GeneralPaperHeaderCountDirectory.data]
    exact h
  refine ⟨hNew,GeneralPaperHeaderCountReadback.compatible model A _ directory hNew,?_⟩
  intro header hh hf
  have hCaps := GeneralPaperReferenceLayoutInstallation.capacities model S A start plan directory.headers hSafe.2.1 hCap
  exact GeneralPaperHeaderCountReadback.count_source model A _ directory hNew header hh hf
    (GeneralPaperHeaderCountExpansion.count_fits header hA (hSafe.2.2.2.1 header hh) (hCaps header hh))

end Blotto.GeneralPaperHeaderCountInstallation
