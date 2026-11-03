import Blotto.GeneralPaperUnifiedFieldMemoryViews

/-! The single directory memory refines both legacy typed heaps exactly.
Computed matrix readers have the same data and local work on either view;
installation-work fields are deliberately not used by a draw reader. -/
namespace Blotto.GeneralPaperUnifiedDirectoryViews
open GeneralPaperFieldDirectory GeneralPaperFieldDirectorySafety GeneralPaperFieldDirectoryPartition
open GeneralPaperUnifiedDirectoryInstallation
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

theorem views (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    (view (install model S A directory)).references = (GeneralPaperFieldDirectoryInstallation.install model S A directory).references ∧
      (view (install model S A directory)).payloads = (GeneralPaperFieldDirectoryInstallation.install model S A directory).payloads ∧
      (view (install model S A directory)).root = (GeneralPaperFieldDirectoryInstallation.install model S A directory).root := by
  have hWords := word_keys model S A start plan directory hSafe hA hCap
  have hScalars := GeneralPaperFieldDirectoryInstallation.scalar_keys model S A start plan directory hSafe hPos hCap
  have hCross := cross_keys model S A start plan directory hSafe hCovered hA hCap
  refine ⟨?_,?_,rfl⟩
  · exact GeneralPaperUnifiedFieldMemoryViews.reference_view S A
      (GeneralPaperReferenceRegionProgram.collect model S A directory.headers).entries
      (directory.cells.map GeneralPaperScalarFieldCursor.Cell.entry) hWords hScalars hCross
  · exact GeneralPaperUnifiedFieldMemoryViews.scalar_view S A
      (GeneralPaperReferenceRegionProgram.collect model S A directory.headers).entries
      (directory.cells.map GeneralPaperScalarFieldCursor.Cell.entry) hWords hScalars hCross

theorem read_ext (model : RationalCostModel) (A : ℕ)
    (first second : GeneralPaperFieldDirectoryInstallation.Installed A)
    (hReferences : first.references = second.references) (hPayloads : first.payloads = second.payloads)
    (hRoot : first.root = second.root) (row column : ℕ) :
    GeneralPaperMatrixFieldRead.read model A first row column = GeneralPaperMatrixFieldRead.read model A second row column := by
  simp only [GeneralPaperMatrixFieldRead.read,hReferences,hPayloads,hRoot]

theorem rational_ext (model : RationalCostModel) (A : ℕ)
    (first second : GeneralPaperFieldDirectoryInstallation.Installed A)
    (hReferences : first.references = second.references) (hPayloads : first.payloads = second.payloads)
    (hRoot : first.root = second.root) (row column : ℕ) :
    GeneralPaperMatrixFieldRead.rational model A first row column = GeneralPaperMatrixFieldRead.rational model A second row column := by
  simp only [GeneralPaperMatrixFieldRead.rational,read_ext model A first second hReferences hPayloads hRoot row column]

theorem matrix_read (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A)
    (row column : ℕ) :
    GeneralPaperMatrixFieldRead.read model A (view (install model S A directory)) row column =
      GeneralPaperMatrixFieldRead.read model A (GeneralPaperFieldDirectoryInstallation.install model S A directory) row column := by
  obtain ⟨hr,hp,hroot⟩ := views model S A start plan directory hSafe hCovered hPos hA hCap
  exact read_ext model A _ _ hr hp hroot row column

theorem matrix_rational (model : RationalCostModel) (S A start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A)
    (row column : ℕ) :
    GeneralPaperMatrixFieldRead.rational model A (view (install model S A directory)) row column =
      GeneralPaperMatrixFieldRead.rational model A (GeneralPaperFieldDirectoryInstallation.install model S A directory) row column := by
  obtain ⟨hr,hp,hroot⟩ := views model S A start plan directory hSafe hCovered hPos hA hCap
  exact rational_ext model A _ _ hr hp hroot row column

end Blotto.GeneralPaperUnifiedDirectoryViews
