import Blotto.GeneralPaperStoredRouteFieldWork
import Blotto.GeneralPaperStoredRouteArraySource

/-! One indexed route access follows its actual record and decodes its
actual fields. The front owner derives count and index capacity, including
when the route array is empty. -/
namespace Blotto.GeneralPaperStoredRouteArrayWork
open GeneralPaperFieldDirectory GeneralPaperSequentialLayout GeneralPaperReferenceRegionSlots
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperStoredReadContext (Context)
open GeneralPaperUnifiedFieldValue
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

def header {n m : ℕ} (model : RationalCostModel) (S A start : ℕ) (routes : FixedArrayTable n (GroupRoute m)) : Header A :=
  let directory := GeneralPaperRouteArrayCursor.expected model S A start routes
  let dirs := GeneralPaperChildDirectorySpecification.directories (GeneralPaperRouteArrayCursor.schema model S A)
    (GeneralPaperRouteFieldCursor.expected model S A) (start + A * (64 + routes.data.toList.length)) routes.data.toList
  ⟨directory.root,64,(dirs.map Directory.root).map Region.reference⟩

def bound (model : RationalCostModel) (A m : ℕ) (coefficient : ℚ) : ℕ :=
  GeneralPaperStoredRouteFieldWork.bound model A m coefficient +
    GeneralPaperStoredReferenceReadWork.readBound model A A + 256 * (A + 1)

def heightBound (model : RationalCostModel) (A m s : ℕ) : ℕ :=
  3 * GeneralPaperStoredScalarReadWork.overhead model A + 2 * GeneralPaperEncodedScalarStorage.natBits m +
    2 * (1 + 2 * s) + GeneralPaperStoredReferenceReadWork.readBound model A A + 512 * (A + 1)

theorem capacity {n m : ℕ} (model : RationalCostModel) (S A layoutStart start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed)
    (routes : FixedArrayTable n (GroupRoute m))
    (hHeaders : ∀ h ∈ (GeneralPaperRouteArrayCursor.expected model S A start routes).headers,h ∈ full.headers) :
    n + 1 < 2 ^ A := by
  have hHeader : header model S A start routes ∈ full.headers := hHeaders _ (List.mem_cons_self ..)
  have hStop := GeneralPaperStoredReadContext.header_capacity ctx _ hHeader
  change start + A * (64 + routes.data.toList.length) < 2 ^ A at hStop
  rw [Array.length_toList,routes.size] at hStop
  have hA := ctx.positive
  nlinarith only [hStop,hA]

theorem height_bound (model : RationalCostModel) (A m s : ℕ) (coefficient : ℚ) (h : RationalHeight coefficient s) :
    bound model A m coefficient ≤ heightBound model A m s := by
  have hWord := rationalWordWidth_of_height h
  unfold bound heightBound GeneralPaperStoredRouteFieldWork.bound
  omega

theorem work {n m : ℕ} (model : RationalCostModel) (S A layoutStart start : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed)
    (routes : FixedArrayTable n (GroupRoute m))
    (hRead : Readback model A installed (GeneralPaperRouteArrayCursor.expected model S A start routes))
    (hFullHeaders : ∀ h ∈ (GeneralPaperRouteArrayCursor.expected model S A start routes).headers,h ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperRouteArrayCursor.expected model S A start routes).root.reference) (index : Fin n) :
    (GeneralPaperRouteArrayRead.read model A installed index.val).2 ≤ bound model A m (routes.read index).2 := by
  let directory := GeneralPaperRouteArrayCursor.expected model S A start routes
  let values := routes.data.toList
  let dirs := GeneralPaperChildDirectorySpecification.directories (GeneralPaperRouteArrayCursor.schema model S A)
    (GeneralPaperRouteFieldCursor.expected model S A) (start + A * (64 + values.length)) values
  have hIndex : index.val < values.length := by dsimp only [values]; rw [Array.length_toList,routes.size]; exact index.isLt
  have hLength : dirs.length = values.length := GeneralPaperChildDirectorySpecification.directory_count _ _ _ _
  have hDirIndex : index.val < dirs.length := by rw [hLength]; exact hIndex
  obtain ⟨fieldStart,hLookup⟩ := GeneralPaperFieldDirectoryLookup.child_lookup (GeneralPaperRouteArrayCursor.schema model S A)
    (GeneralPaperRouteFieldCursor.expected model S A) (start + A * (64 + values.length)) values index.val hIndex
  have hValue : values[index.val] = routes.read index := by simp only [values,Array.getElem_toList,FixedArrayTable.read]
  rw [hValue,List.getElem?_eq_getElem hDirIndex] at hLookup
  let child := GeneralPaperRouteFieldCursor.expected model S A (routes.read index) fieldStart
  have hEq : dirs[index.val] = child := Option.some.inj hLookup
  have hChild : child ∈ dirs := by rw [← hEq]; exact List.getElem_mem hDirIndex
  let header : Header A := ⟨directory.root,64,(dirs.map Directory.root).map Region.reference⟩
  have hHeader : header ∈ directory.headers := List.mem_cons_self ..
  have hTargetIndex : index.val < header.targets.length := by
    change index.val < ((dirs.map Directory.root).map Region.reference).length
    rw [List.length_map,List.length_map,hLength]
    exact hIndex
  have hTarget : header.targets[index.val]? = some child.root.reference := by
    change ((dirs.map Directory.root).map Region.reference)[index.val]? = _
    rw [List.getElem?_map,List.getElem?_map,List.getElem?_eq_getElem hDirIndex,hEq]
    rfl
  rw [List.getElem?_eq_getElem hTargetIndex] at hTarget
  have hPointer := hRead.1 header hHeader ⟨index.val,hTargetIndex⟩
  rw [Option.some.inj hTarget] at hPointer
  change (GeneralPaperMixedReferenceRegionProgram.read model A (referenceMemory installed.memory) directory.root.reference 64 index.val).1 =
    some (⟨A,child.root.reference⟩ : Word) at hPointer
  rw [← hRoot] at hPointer
  have hHeaders : ∀ h ∈ child.headers,h ∈ directory.headers := by
    intro h hh
    exact List.mem_cons_of_mem header (GeneralPaperFieldDirectoryLookup.collect_header_member dirs child hChild h hh)
  have hCells : ∀ c ∈ child.cells,c ∈ directory.cells := by
    intro c hc
    exact GeneralPaperFieldDirectoryLookup.collect_cell_member dirs child hChild c hc
  have hChildRead := GeneralPaperHeaderCountReadback.restrict model A installed directory child hRead hHeaders hCells
  have hRoute := GeneralPaperStoredRouteReadback.source model S A fieldStart
    (GeneralPaperStoredScalarRead.atRoot installed child.root.reference) (routes.read index) hChildRead rfl
  have hRouteWork := GeneralPaperStoredRouteFieldWork.work model S A layoutStart fieldStart plan full
    (GeneralPaperStoredScalarRead.atRoot installed child.root.reference) (GeneralPaperStoredReadContext.atRoot ctx child.root.reference)
    (routes.read index) hChildRead (fun h hh => hFullHeaders h (hHeaders h hh)) rfl
  have hCount := GeneralPaperStoredReadContext.header_count_fits ctx header (hFullHeaders header hHeader)
  have hPointerWork := GeneralPaperStoredReferenceReadWork.read_work model A A 64 index.val _ installed.root child.root.reference
    le_rfl (hTargetIndex.trans hCount) hPointer
  rw [(GeneralPaperRouteArrayRead.trace model A installed index.val child.root.reference _ hPointer hRoute).2]
  unfold bound
  dsimp only [GeneralPaperStoredScalarRead.atRoot] at hRouteWork
  omega

end Blotto.GeneralPaperStoredRouteArrayWork
