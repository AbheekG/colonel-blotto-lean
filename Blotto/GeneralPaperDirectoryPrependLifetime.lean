import Blotto.GeneralPaperDirectoryAppendLifetime

/-! Complete local prepend lifetime at actual safe measured directories.
The caller owns one right-tail body. Output suffixes share that body; only
the current child records/copies and local activations are charged here. -/
namespace Blotto.GeneralPaperDirectoryPrependLifetime
open GeneralPaperFieldDirectory (Directory Body prepend)
open GeneralPaperFieldDirectorySafety (Safe SafeBody)
open GeneralPaperMeasuredBlockPlan (Plan)
open GeneralPaperEncodedScalarStorage
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit unit_bounds)
open GeneralPaperPayloadInstallationLifetime (cap)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def bodyFoot {A : ℕ} (S : ℕ) (body : Body A) : ℕ :=
  GeneralPaperMeasuredLayoutStorage.regionsFoot S body.roots +
    listFootprint S (GeneralPaperFieldDirectoryStorage.headerFoot S) body.headers +
    listFootprint S (GeneralPaperFieldDirectoryStorage.cellFoot S) body.cells + 64 * S

theorem output_owner (S A : ℕ) (directory : Directory A) (tail : Body A) :
    bodyFoot S (prepend S A directory tail).1 ≤ bodyFoot S tail +
      GeneralPaperFieldDirectoryStorage.directoryFoot S directory + 2 * S := by
  unfold bodyFoot
  rw [GeneralPaperFieldDirectory.prepend_roots,GeneralPaperFieldDirectory.prepend_headers,GeneralPaperFieldDirectory.prepend_cells]
  simp only [GeneralPaperMeasuredLayoutStorage.regionsFoot,GeneralPaperFieldDirectoryStorage.directoryFoot,listFootprint,List.map_append,List.sum_append,
    List.length_append,List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
  omega

def controls (S A : ℕ) (directory : Directory A) (tail : Body A) : List ℕ :=
  let headers := GeneralPaperFieldDirectory.appendHeaders S A directory.headers tail.headers
  let cells := GeneralPaperFieldDirectory.appendCells S A directory.cells tail.cells
  [S,A,headers.2,cells.2,headers.2+cells.2,GeneralPaperLastRegionSelection.price S A directory.root,
    headers.2+cells.2+GeneralPaperLastRegionSelection.price S A directory.root,(prepend S A directory tail).2]

def localWindow (S A : ℕ) (directory : Directory A) (tail : Body A) : ℕ :=
  GeneralPaperFieldDirectoryStorage.directoryFoot S directory +
    GeneralPaperDirectoryAppendLifetime.headerFrames S A directory.headers tail.headers +
    GeneralPaperDirectoryAppendLifetime.cellFrames S A directory.cells tail.cells +
    GeneralPaperMeasuredLayoutStorage.regionFoot S directory.root + GeneralPaperLastRegionSelection.price S A directory.root +
    fields S (controls S A directory tail) + 192 * S

theorem local_bound (model : RationalCostModel) (S A start Q : ℕ) (plan : Plan) (directory : Directory A) (tail : Body A)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A)
    (hCap : start + plan.sizes.sum < 2 ^ A) (hWork : (prepend S A directory tail).2 ≤ Q) :
    localWindow S A directory tail ≤ (plan.sizes.sum + 1) * 40 * unit model S A Q := by
  have hWhole := hWork
  change (GeneralPaperFieldDirectory.appendHeaders S A directory.headers tail.headers).2 +
    (GeneralPaperFieldDirectory.appendCells S A directory.cells tail.cells).2 +
    GeneralPaperLastRegionSelection.price S A directory.root + 64 * (S + A + 1) ≤ Q at hWork
  have hRange := GeneralPaperMeasuredBlockLayout.range model S A start plan
  have hRootCap := (hRange directory.root hSafe.1).2.trans_lt hCap
  have hHeaderCaps := GeneralPaperReferenceLayoutInstallation.capacities model S A start plan directory.headers hSafe.2.1 hCap
  have hCellCaps : ∀ cell ∈ directory.cells,cell.region.stop < 2 ^ A := by
    intro cell hc
    exact (hRange cell.region (hSafe.2.2.1.subset (List.mem_map.mpr ⟨cell,hc,rfl⟩))).2.trans_lt hCap
  have hHeaders := GeneralPaperDirectoryAppendLifetime.header_frames_bound model S A Q directory.headers tail.headers
    hA hSafe.2.2.2.1 hHeaderCaps (by omega)
  have hCells := GeneralPaperDirectoryAppendLifetime.cell_frames_bound model S A Q directory.cells tail.cells hA hCellCaps (by omega)
  have hDirectory := GeneralPaperFieldDirectoryStorage.directory_bound model S A start plan directory hSafe hPos hA hCap
  have hCounts := GeneralPaperStoredDirectoryPreparationWork.directory_counts model S A start plan directory hSafe hPos
  have hSlots := GeneralPaperReferenceHeaderSlotArea.layout_count model S A start plan directory.headers hSafe.2.1 hA hSafe.2.2.2.1
  have hArea := GeneralPaperDirectoryCopyWork.payload_area model S A start plan directory hSafe
  have hRegion := GeneralPaperMeasuredLayoutStorage.region_bound S A directory.root hA hRootCap
  have hRead := GeneralPaperDirectoryCopyWork.region_work model S A directory.root hA hRootCap
  have hFields := fields_bound S (natBits (cap S A Q)) (controls S A directory tail) (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 8 * (natBits (cap S A Q) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S A Q
  have hHeaderMass := Nat.mul_le_mul_right (12 * unit model S A Q)
    (show GeneralPaperReferenceHeaderSlotArea.slots directory.headers + directory.headers.length + 1 ≤ 2 * (plan.sizes.sum + 1) by omega)
  have hCellMass := Nat.mul_le_mul_right (unit model S A Q) (Nat.add_le_add_right hCounts.2 1)
  have hDirFactor := Nat.mul_le_mul_left (plan.sizes.sum + 1) (show 2048 * (S + A + 1) ≤ unit model S A Q by omega)
  have hPayload := Nat.mul_le_mul_left plan.sizes.sum (show 2 ≤ unit model S A Q by omega)
  have hParent : GeneralPaperMeasuredLayoutStorage.regionFoot S directory.root + GeneralPaperLastRegionSelection.price S A directory.root +
      fields S (controls S A directory tail) + 192 * S ≤ unit model S A Q := by
    unfold GeneralPaperMeasuredLayoutStorage.regionBound at hRegion
    omega
  have hBase := Nat.mul_le_mul_right (unit model S A Q) (show 1 ≤ plan.sizes.sum + 1 by omega)
  unfold localWindow GeneralPaperFieldDirectoryStorage.bound at *
  nlinarith only [hHeaders,hCells,hDirectory,hHeaderMass,hCellMass,hDirFactor,hArea,hPayload,hParent,hBase]

def window (S A : ℕ) (directory : Directory A) (tail : Body A) : ℕ := bodyFoot S tail + localWindow S A directory tail

theorem caller_bound (model : RationalCostModel) (S A start Q : ℕ) (plan : Plan) (directory : Directory A) (tail : Body A)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A)
    (hCap : start + plan.sizes.sum < 2 ^ A) (hWork : (prepend S A directory tail).2 ≤ Q) :
    window S A directory tail ≤ bodyFoot S tail + (plan.sizes.sum + 1) * 40 * unit model S A Q :=
  Nat.add_le_add_left (local_bound model S A start Q plan directory tail hSafe hPos hA hCap hWork) _

theorem result_is_covered (S A : ℕ) (directory : Directory A) (tail : Body A) :
    bodyFoot S (prepend S A directory tail).1 ≤ window S A directory tail := by
  have h := output_owner S A directory tail
  unfold window localWindow
  omega

end Blotto.GeneralPaperDirectoryPrependLifetime
