import Blotto.GeneralPaperOuterFieldCursorLifetime

/-! Complete actual directory-memory extension. Collection, typed cell
mapping, unified installation, source directory and saved parent prices
coexist with incoming/final resident RAM. Each scalar keeps its own width. -/
namespace Blotto.GeneralPaperDirectoryExtensionLifetime
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperFieldDirectorySafety (Safe)
open GeneralPaperFieldDirectoryPartition (Covered)
open GeneralPaperMeasuredBlockPlan (Plan)
open GeneralPaperScalarFieldCursor (Cell)
open GeneralPaperUnifiedFieldValue (Memory encode)
open GeneralPaperPayloadMemoryOwnership (Bounded cellSize)
open GeneralPaperEncodedScalarStorage
open GeneralPaperPayloadInstallationLifetime (cap)
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def cellFrames (S A : ℕ) (cells : List (Cell A)) : ℕ :=
  GeneralPaperUnifiedInstallationLifetime.liftFrames S A (GeneralPaperFieldDirectoryStorage.cellFoot S) (fun _ => 0) cells

def cellProfile (S A B : ℕ) : ℕ :=
  B + (B + 1) * (192 * (S + A + 1) + GeneralPaperUnifiedInstallationLifetime.liftFrameBound S A 0)

theorem cell_frames_bound (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (directory : Directory A)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    cellFrames S A directory.cells ≤ cellProfile S A plan.sizes.sum := by
  have hFrames := GeneralPaperUnifiedInstallationLifetime.lift_frames_bound S A 0
    (GeneralPaperFieldDirectoryStorage.cellFoot S) (fun _ : List (Cell A) => 0) directory.cells
    (fun _ _ => le_rfl) le_rfl
  have hRange := GeneralPaperMeasuredBlockLayout.range model S A start plan
  have hCells := GeneralPaperFieldDirectoryStorage.cells_bound S A directory.cells (by
    intro cell hc
    have hm := hSafe.2.2.1.subset (List.mem_map.mpr ⟨cell,hc,rfl⟩)
    exact GeneralPaperMeasuredLayoutStorage.region_bound S A cell.region hA ((hRange cell.region hm).2.trans_lt hCap))
  have hCounts := GeneralPaperStoredDirectoryPreparationWork.directory_counts model S A start plan directory hSafe hPos
  have hArea := GeneralPaperDirectoryCopyWork.payload_area model S A start plan directory hSafe
  have hCountPay := Nat.mul_le_mul_right (192 * (S + A + 1) + GeneralPaperUnifiedInstallationLifetime.liftFrameBound S A 0)
    (Nat.add_le_add_right hCounts.2 1)
  unfold cellFrames cellProfile
  nlinarith only [hFrames,hCells,hArea,hCountPay]

def controls (model : RationalCostModel) (S A : ℕ) (directory : Directory A) (memory : Memory) : List ℕ :=
  let words := GeneralPaperReferenceRegionProgram.collect model S A directory.headers
  let actual := GeneralPaperUnifiedFieldMemory.prepare S A words.entries (directory.cells.map Cell.entry) memory
  [S,A,words.work,actual.2,words.work + actual.2,(GeneralPaperStoredDirectoryExtension.install model S A directory memory).work]

def extraWindow (model : RationalCostModel) (S A : ℕ) (directory : Directory A) (memory : Memory) : ℕ :=
  GeneralPaperDirectoryReferenceCollectionLifetime.window model S A directory +
    GeneralPaperFieldDirectoryStorage.directoryFoot S directory + cellFrames S A directory.cells +
    fields S (controls model S A directory memory) + 128 * S

def extraProfile (model : RationalCostModel) (S A B : ℕ) : ℕ :=
  GeneralPaperDirectoryReferenceCollectionLifetime.profile model S A B + GeneralPaperFieldDirectoryStorage.bound S A B +
    cellProfile S A B + 6 * (natBits (cap S A (GeneralPaperStoredDirectoryPreparationWork.installBound model S A B)) + S) + 160 * S

theorem extra_window_bound (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (directory : Directory A) (memory : Memory)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    extraWindow model S A directory memory ≤ extraProfile model S A plan.sizes.sum := by
  have hCollection := GeneralPaperDirectoryReferenceCollectionLifetime.window_bound model S A start plan directory hSafe hPos hA hCap
  have hDirectory := GeneralPaperFieldDirectoryStorage.directory_bound model S A start plan directory hSafe hPos hA hCap
  have hMap := cell_frames_bound model S A start plan directory hSafe hPos hA hCap
  have hWhole := GeneralPaperStoredDirectoryPreparationWork.extension_work model S A start plan directory memory hSafe hCovered hPos hA hCap
  have hWork := hWhole
  change (GeneralPaperReferenceRegionProgram.collect model S A directory.headers).work +
    (GeneralPaperUnifiedFieldMemory.prepare S A (GeneralPaperReferenceRegionProgram.collect model S A directory.headers).entries
      (directory.cells.map Cell.entry) memory).2 + 128 * (S + A + 1) ≤ _ at hWork
  have hFields := fields_bound S (natBits (cap S A (GeneralPaperStoredDirectoryPreparationWork.installBound model S A plan.sizes.sum)))
    (controls model S A directory memory) (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 6 * (natBits (cap S A (GeneralPaperStoredDirectoryPreparationWork.installBound model S A plan.sizes.sum)) + S) + 32 * S at hFields
  unfold extraWindow extraProfile
  omega

def window (model : RationalCostModel) (S A : ℕ) (directory : Directory A) (memory : Memory) : ℕ :=
  GeneralPaperDirectoryInstallationLifetime.window model S A directory memory + extraWindow model S A directory memory

def profile (model : RationalCostModel) (S A B : ℕ) : ℕ :=
  GeneralPaperDirectoryInstallationLifetime.profile model S A B + extraProfile model S A B

theorem window_bound (model : RationalCostModel) (S A start : ℕ) (plan : Plan) (directory : Directory A) (memory : Memory)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    window model S A directory memory ≤ profile model S A plan.sizes.sum :=
  Nat.add_le_add (GeneralPaperDirectoryInstallationLifetime.window_bound model S A start plan directory memory hSafe hCovered hPos hA hCap)
    (extra_window_bound model S A start plan directory memory hSafe hCovered hPos hA hCap)

theorem resident_coexistence (model : RationalCostModel) (S A start B : ℕ) (plan : Plan) (directory : Directory A)
    (memory : Memory) (hMemory : Bounded encode memory B)
    (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hCovered : Covered (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A) (hCap : start + plan.sizes.sum < 2 ^ A) :
    ∃ keys : Finset ℕ,(∀ key,(GeneralPaperStoredDirectoryExtension.install model S A directory memory).memory key ≠ none → key ∈ keys) ∧
      (∑ key ∈ keys,cellSize encode (GeneralPaperStoredDirectoryExtension.install model S A directory memory).memory key) +
        window model S A directory memory ≤ B + plan.sizes.sum + profile model S A plan.sizes.sum := by
  obtain ⟨keys,hSupport,hInstall⟩ := GeneralPaperDirectoryInstallationLifetime.resident_coexistence
    model S A start B plan directory memory hMemory hSafe hCovered hPos hA hCap
  have hExtra := extra_window_bound model S A start plan directory memory hSafe hCovered hPos hA hCap
  refine ⟨keys,hSupport,?_⟩
  dsimp only [window,profile]
  omega

theorem profile_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A B r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x)
    (hS : Tight S L) (hA : Tight A L) (hB : Bound B r L) (hrSmall : Small r L) :
    Bound (fun x => profile model (S x) (A x) (B x)) r L := by
  have hInstall := GeneralPaperDirectoryInstallationLifetime.profile_rate model hFast S A B r L hL hr hS hA hB hrSmall
  have hCollection := GeneralPaperReferenceCollectionLifetimeRates.profile_rate model hFast S A B r L hL hr hS hA hB hrSmall
  have hDirectory := GeneralPaperMeasuredDirectoryStorageRates.directory_rate S A B r L hL hr hS hA hB
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  have hFrame := GeneralPaperUnifiedInstallationLifetime.lift_frame_rate S A (fun _ => 0) L hL hS hA (small_constant 0 L hL)
  have hAllWork := GeneralPaperStoredPreparationWorkRates.directory_rate model hFast S A B r L hL hr hS hA hB
  have hWork : Bound (fun x => GeneralPaperStoredDirectoryPreparationWork.installBound model (S x) (A x) (B x)) r L := by
    apply dominated hAllWork
    intro x
    unfold GeneralPaperStoredDirectoryPreparationWork.bound
    omega
  have hQ := bound_small hL hWork hrSmall
  have hSSmall := small_of_tight hS hL
  have hASmall := small_of_tight hA hL
  have hCap : Small (fun x => cap (S x) (A x) (GeneralPaperStoredDirectoryPreparationWork.installBound model (S x) (A x) (B x))) L := by
    unfold cap
    fun_prop
  have hBits := polylog_bits _ L hL hCap
  have hMapFactor : Polylog (fun x => 192 * (S x + A x + 1) + GeneralPaperUnifiedInstallationLifetime.liftFrameBound (S x) (A x) 0) L := by fun_prop
  have hMap := bound_mul_polylog _ _ r L (show Bound (fun x => B x + 1) r L by fun_prop) hMapFactor
  unfold profile extraProfile cellProfile
  fun_prop (config := {maxSteps := 30000})

end Blotto.GeneralPaperDirectoryExtensionLifetime
