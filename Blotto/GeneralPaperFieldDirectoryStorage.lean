import Blotto.GeneralPaperMeasuredLayoutStorage

/-! Complete owned temporary-directory data: roots, region descriptors,
header controls and target lists, scalar payloads and list/record links.
Safe actual layouts pay for each payload by a single sum of widths. The
count-expanded directory is covered with the original directory still live. -/
namespace Blotto.GeneralPaperFieldDirectoryStorage
open GeneralPaperEncodedScalarStorage GeneralPaperMeasuredLayoutStorage
open GeneralPaperFieldDirectory GeneralPaperFieldDirectorySafety
open GeneralPaperSequentialLayout GeneralPaperReferenceRegionSlots
open GeneralPaperScalarFieldCursor (Cell)
open GeneralPaperRetainedScalarValue (encode)
open GeneralPaperMeasuredBlockPlan (Plan)
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def headerFoot {A : ℕ} (S : ℕ) (header : Header A) : ℕ :=
  regionFoot S header.region + fields S [header.fixed] +
    listFootprint S (fun _ : FixedBinaryWord A => A) header.targets + 64 * S

def cellFoot {A : ℕ} (S : ℕ) (cell : Cell A) : ℕ :=
  regionFoot S cell.region + encode cell.value + 64 * S

def directoryFoot {A : ℕ} (S : ℕ) (directory : Directory A) : ℕ :=
  regionFoot S directory.root + listFootprint S (headerFoot S) directory.headers +
    listFootprint S (cellFoot S) directory.cells + 64 * S

def bound (S A B : ℕ) : ℕ := (B + 1) * 2048 * (S + A + 1)

theorem header_bound (S A : ℕ) (header : Header A) (hA : 0 < A)
    (hValid : GeneralPaperReferenceRegionSlots.Valid header) (hCap : header.region.stop < 2 ^ A) :
    headerFoot S header ≤ (header.targets.length + 1) * 384 * (S + A + 1) := by
  have hRegion := region_bound S A header.region hA hCap
  obtain ⟨_,_,hFixed,_⟩ := GeneralPaperStoredHeaderPreparationWork.owner_widths header hA hValid hCap
  have hTargets := list_bound S A (fun _ : FixedBinaryWord A => A) header.targets (fun _ _ => le_rfl)
  have hTargetWidth := Nat.mul_le_mul_left header.targets.length
    (show A + 2 * S ≤ 384 * (S + A + 1) by omega)
  unfold headerFoot fields natBits
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  unfold regionBound at hRegion
  nlinarith only [hRegion,hFixed,hTargets,hTargetWidth]

theorem headers_bound (S A : ℕ) (headers : List (Header A)) (hA : 0 < A)
    (hValid : ∀ header ∈ headers,GeneralPaperReferenceRegionSlots.Valid header)
    (hCap : ∀ header ∈ headers,header.region.stop < 2 ^ A) :
    (headers.map (headerFoot S)).sum ≤
      (GeneralPaperReferenceHeaderSlotArea.slots headers + headers.length) * 384 * (S + A + 1) := by
  induction headers with
  | nil => simp only [GeneralPaperReferenceHeaderSlotArea.slots,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_add,Nat.zero_mul,le_refl]
  | cons header headers ih =>
    have hHead := header_bound S A header hA (hValid header (List.mem_cons_self ..)) (hCap header (List.mem_cons_self ..))
    have hTail := ih (fun h hh => hValid h (List.mem_cons_of_mem _ hh)) (fun h hh => hCap h (List.mem_cons_of_mem _ hh))
    simp only [List.map_cons,List.sum_cons,List.length_cons,GeneralPaperReferenceHeaderSlotArea.slots] at hTail ⊢
    nlinarith only [hHead,hTail]

theorem cells_bound (S A : ℕ) (cells : List (Cell A))
    (hRegion : ∀ cell ∈ cells,regionFoot S cell.region ≤ regionBound S A) :
    (cells.map (cellFoot S)).sum ≤ (cells.map (fun cell => encode cell.value)).sum +
      cells.length * 192 * (S + A + 1) := by
  induction cells with
  | nil => simp only [List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons cell cells ih =>
    have hHead := hRegion cell (List.mem_cons_self ..)
    have hTail := ih (fun c hc => hRegion c (List.mem_cons_of_mem _ hc))
    simp only [List.map_cons,List.sum_cons,List.length_cons,cellFoot]
    unfold regionBound at hHead
    nlinarith only [hHead,hTail]

theorem directory_bound (model : RationalCostModel) (S A start : ℕ) (plan : Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A)
    (hCap : start + plan.sizes.sum < 2 ^ A) : directoryFoot S directory ≤ bound S A plan.sizes.sum := by
  have hRange := GeneralPaperMeasuredBlockLayout.range model S A start plan
  have hRegions : ∀ region ∈ (GeneralPaperMeasuredBlockLayout.run model S A start plan).1,
      regionFoot S region ≤ regionBound S A := by
    intro region hr
    exact region_bound S A region hA ((hRange region hr).2.trans_lt hCap)
  have hRoot := hRegions directory.root hSafe.1
  have hCaps := GeneralPaperReferenceLayoutInstallation.capacities model S A start plan directory.headers hSafe.2.1 hCap
  have hHeaders := headers_bound S A directory.headers hA hSafe.2.2.2.1 hCaps
  have hCells := cells_bound S A directory.cells (fun cell hc =>
    hRegions cell.region (hSafe.2.2.1.subset (List.mem_map.mpr ⟨cell,hc,rfl⟩)))
  have hCounts := GeneralPaperStoredDirectoryPreparationWork.directory_counts model S A start plan directory hSafe hPos
  have hSlots := GeneralPaperReferenceHeaderSlotArea.layout_count model S A start plan directory.headers hSafe.2.1 hA hSafe.2.2.2.1
  have hArea := GeneralPaperDirectoryCopyWork.payload_area model S A start plan directory hSafe
  have hH := Nat.mul_le_mul_right (384 * (S + A + 1))
    (show GeneralPaperReferenceHeaderSlotArea.slots directory.headers + directory.headers.length ≤ 2 * plan.sizes.sum by omega)
  have hC := Nat.mul_le_mul_right (192 * (S + A + 1)) hCounts.2
  have hLinks := Nat.mul_le_mul_right (2 * S)
    (show directory.headers.length + directory.cells.length ≤ 2 * plan.sizes.sum by omega)
  have hPayload := Nat.mul_le_mul_left plan.sizes.sum (show 1 ≤ S + A + 1 by omega)
  unfold directoryFoot listFootprint bound
  unfold regionBound at hRoot
  nlinarith only [hRoot,hHeaders,hCells,hH,hC,hLinks,hArea,hPayload]

theorem count_expanded_bound (model : RationalCostModel) (S A start : ℕ) (plan : Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A)
    (hCap : start + plan.sizes.sum < 2 ^ A) :
    directoryFoot S (GeneralPaperHeaderCountDirectory.prepare model S A directory).1 ≤ bound S A plan.sizes.sum := by
  rw [GeneralPaperHeaderCountDirectory.data]
  exact directory_bound model S A start plan _ (GeneralPaperHeaderCountDirectory.safe _ directory hSafe) hPos hA hCap

def countWindow (model : RationalCostModel) (S A : ℕ) (directory : Directory A) : ℕ :=
  directoryFoot S directory + directoryFoot S (GeneralPaperHeaderCountDirectory.prepare model S A directory).1 +
    fields S [(GeneralPaperHeaderCountDirectory.prepare model S A directory).2] + 64 * S

def countBound (model : RationalCostModel) (S A B : ℕ) : ℕ :=
  2 * bound S A B + natBits (GeneralPaperStoredDirectoryPreparationWork.countBound model S A B) + 97 * S

theorem count_window_bound (model : RationalCostModel) (S A start : ℕ) (plan : Plan)
    (directory : Directory A) (hSafe : Safe (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 directory)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A)
    (hCap : start + plan.sizes.sum < 2 ^ A) :
    countWindow model S A directory ≤ countBound model S A plan.sizes.sum := by
  have hOriginal := directory_bound model S A start plan directory hSafe hPos hA hCap
  have hExpanded := count_expanded_bound model S A start plan directory hSafe hPos hA hCap
  have hWork := GeneralPaperStoredDirectoryPreparationWork.count_work model S A start plan directory hSafe hPos hA hCap
  have hPrice := Nat.add_le_add_left (binaryWordWidth_mono hWork) 1
  change natBits (GeneralPaperHeaderCountDirectory.prepare model S A directory).2 ≤
    natBits (GeneralPaperStoredDirectoryPreparationWork.countBound model S A plan.sizes.sum) at hPrice
  unfold countWindow countBound fields
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  omega

end Blotto.GeneralPaperFieldDirectoryStorage
