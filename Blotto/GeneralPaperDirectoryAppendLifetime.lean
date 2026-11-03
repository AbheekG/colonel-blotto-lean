import Blotto.GeneralPaperDirectoryHeaderCopyLifetime

/-! Actual left-only header/cell directory append activations. Local
header target mass and scalar payload widths are summed once; shared right
tails have one enclosing owner. No ancestor rescan or tail copy is charged. -/
namespace Blotto.GeneralPaperDirectoryAppendLifetime
open GeneralPaperFieldDirectory (appendHeaders appendCells)
open GeneralPaperReferenceRegionSlots (Header Valid)
open GeneralPaperScalarFieldCursor (Cell)
open GeneralPaperRetainedScalarValue (encode)
open GeneralPaperEncodedScalarStorage
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit unit_bounds)
open GeneralPaperPayloadInstallationLifetime (cap)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def headerControls (S A : ℕ) (header : Header A) (headers rest : List (Header A)) : List ℕ :=
  [(GeneralPaperFieldDirectory.copyHeader S A header).2,(appendHeaders S A headers rest).2,
    (GeneralPaperFieldDirectory.copyHeader S A header).2 + (appendHeaders S A headers rest).2,
    (appendHeaders S A (header :: headers) rest).2,S,A]

def headerFrames (S A : ℕ) : List (Header A) → List (Header A) → ℕ
  | [],rest => fields S [S,A,(appendHeaders S A [] rest).2] + 64 * S
  | header :: headers,rest => GeneralPaperDirectoryHeaderCopyLifetime.window S A header +
    GeneralPaperFieldDirectoryStorage.headerFoot S header + fields S (headerControls S A header headers rest) + 128 * S +
    headerFrames S A headers rest

theorem header_frames_bound (model : RationalCostModel) (S A Q : ℕ) (headers rest : List (Header A))
    (hA : 0 < A) (hValid : ∀ h ∈ headers,Valid h) (hCap : ∀ h ∈ headers,h.region.stop < 2 ^ A)
    (hWork : (appendHeaders S A headers rest).2 ≤ Q) :
    headerFrames S A headers rest ≤
      (GeneralPaperReferenceHeaderSlotArea.slots headers + headers.length + 1) * 12 * unit model S A Q := by
  induction headers with
  | nil =>
    have hFields := fields_bound S (natBits (cap S A Q)) [S,A,(appendHeaders S A [] rest).2] (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      unfold cap
      rcases hx with rfl|rfl|rfl <;> omega)
    change fields S _ ≤ 3 * (natBits (cap S A Q) + S) + 32 * S at hFields
    have hUnit := unit_bounds model S A Q
    simp only [headerFrames,GeneralPaperReferenceHeaderSlotArea.slots,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_add,Nat.one_mul]
    omega
  | cons header headers ih =>
    have hWhole := hWork
    change (GeneralPaperFieldDirectory.copyHeader S A header).2 + (appendHeaders S A headers rest).2 + 64 * (S + A + 1) ≤ Q at hWork
    have hh : header ∈ header :: headers := List.mem_cons_self ..
    have hCopy := GeneralPaperDirectoryHeaderCopyLifetime.window_bound model S A Q header hA (hValid header hh) (hCap header hh) (by omega)
    have hHeader := GeneralPaperFieldDirectoryStorage.header_bound S A header hA (hValid header hh) (hCap header hh)
    have ht := ih (fun h hm => hValid h (List.mem_cons_of_mem _ hm)) (fun h hm => hCap h (List.mem_cons_of_mem _ hm)) (by omega)
    have hFields := fields_bound S (natBits (cap S A Q)) (headerControls S A header headers rest) (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [headerControls,List.mem_cons,List.not_mem_nil,or_false] at hx
      unfold cap
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
    change fields S _ ≤ 6 * (natBits (cap S A Q) + S) + 32 * S at hFields
    have hUnit := unit_bounds model S A Q
    have hPay := Nat.mul_le_mul_left (header.targets.length + 1) (show 384 * (S + A + 1) ≤ unit model S A Q by omega)
    have hParent : fields S (headerControls S A header headers rest) + 128 * S ≤ unit model S A Q := by omega
    simp only [headerFrames,GeneralPaperReferenceHeaderSlotArea.slots,List.map_cons,List.sum_cons,List.length_cons] at ht ⊢
    nlinarith only [hCopy,hHeader,ht,hPay,hParent,Nat.zero_le (header.targets.length * unit model S A Q)]

def cellControls (S A : ℕ) (cell : Cell A) (cells rest : List (Cell A)) : List ℕ :=
  [S,A,(appendCells S A cells rest).2,GeneralPaperLastRegionSelection.price S A cell.region,
    (appendCells S A cells rest).2 + GeneralPaperLastRegionSelection.price S A cell.region,
    (appendCells S A cells rest).2 + GeneralPaperLastRegionSelection.price S A cell.region + encode cell.value,
    (appendCells S A (cell :: cells) rest).2]

def cellFrames (S A : ℕ) : List (Cell A) → List (Cell A) → ℕ
  | [],rest => fields S [S,A,(appendCells S A [] rest).2] + 64 * S
  | cell :: cells,rest => GeneralPaperFieldDirectoryStorage.cellFoot S cell + encode cell.value +
    GeneralPaperLastRegionSelection.price S A cell.region + fields S (cellControls S A cell cells rest) + 128 * S + cellFrames S A cells rest

theorem cell_frames_bound (model : RationalCostModel) (S A Q : ℕ) (cells rest : List (Cell A)) (hA : 0 < A)
    (hCap : ∀ cell ∈ cells,cell.region.stop < 2 ^ A) (hWork : (appendCells S A cells rest).2 ≤ Q) :
    cellFrames S A cells rest ≤ 2 * (cells.map (fun cell => encode cell.value)).sum + (cells.length + 1) * unit model S A Q := by
  induction cells with
  | nil =>
    have hFields := fields_bound S (natBits (cap S A Q)) [S,A,(appendCells S A [] rest).2] (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      unfold cap
      rcases hx with rfl|rfl|rfl <;> omega)
    change fields S _ ≤ 3 * (natBits (cap S A Q) + S) + 32 * S at hFields
    have hUnit := unit_bounds model S A Q
    simp only [cellFrames,List.map_nil,List.sum_nil,List.length_nil,Nat.mul_zero,Nat.zero_add,Nat.one_mul]
    omega
  | cons cell cells ih =>
    have hWhole := hWork
    change (appendCells S A cells rest).2 + GeneralPaperLastRegionSelection.price S A cell.region + encode cell.value + 64 * (S + A + 1) ≤ Q at hWork
    have hh : cell ∈ cell :: cells := List.mem_cons_self ..
    have hRegion := GeneralPaperMeasuredLayoutStorage.region_bound S A cell.region hA (hCap cell hh)
    have hRead := GeneralPaperDirectoryCopyWork.region_work model S A cell.region hA (hCap cell hh)
    have ht := ih (fun c hc => hCap c (List.mem_cons_of_mem _ hc)) (by omega)
    have hFields := fields_bound S (natBits (cap S A Q)) (cellControls S A cell cells rest) (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [cellControls,List.mem_cons,List.not_mem_nil,or_false] at hx
      unfold cap
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
    change fields S _ ≤ 7 * (natBits (cap S A Q) + S) + 32 * S at hFields
    have hUnit := unit_bounds model S A Q
    unfold GeneralPaperMeasuredLayoutStorage.regionBound at hRegion
    have hLocal : GeneralPaperFieldDirectoryStorage.cellFoot S cell + encode cell.value + GeneralPaperLastRegionSelection.price S A cell.region +
        fields S (cellControls S A cell cells rest) + 128 * S ≤ 2 * encode cell.value + unit model S A Q := by
      unfold GeneralPaperFieldDirectoryStorage.cellFoot
      omega
    simp only [cellFrames,List.map_cons,List.sum_cons,List.length_cons]
    nlinarith only [ht,hLocal]

theorem header_shared_suffix (S A : ℕ) (headers rest : List (Header A)) :
    (appendHeaders S A headers rest).1.drop headers.length = rest := by
  rw [GeneralPaperFieldDirectory.append_headers_data]
  exact List.drop_left

theorem cell_shared_suffix (S A : ℕ) (cells rest : List (Cell A)) :
    (appendCells S A cells rest).1.drop cells.length = rest := by
  rw [GeneralPaperFieldDirectory.append_cells_data]
  exact List.drop_left

end Blotto.GeneralPaperDirectoryAppendLifetime
