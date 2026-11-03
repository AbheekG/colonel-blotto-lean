import Blotto.GeneralPaperMappedScalarArrayInstallation

/-! Temporary field directories collect actual roots, reference-bearing
headers and scalar payload entries. Priced append copies only its left child
list, so aggregation does not rescan the already produced suffix. Directories
are construction metadata, not additional retained sampler fields. -/
namespace Blotto.GeneralPaperFieldDirectory
open GeneralPaperSequentialLayout GeneralPaperReferenceRegionSlots
open GeneralPaperScalarFieldCursor (Cell)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

structure Directory (A : ℕ) where
  root : Region A
  headers : List (Header A)
  cells : List (Cell A)

def ofArray {A : ℕ} (fields : GeneralPaperScalarArrayFieldCursor.Fields A) : Directory A :=
  ⟨fields.header.region,[fields.header],fields.cells⟩

def copyHeader (S A : ℕ) (header : Header A) : Header A × ℕ :=
  let targets := GeneralPaperReferenceCopy.list S S (GeneralPaperReferenceCopy.scalar S S (fun _ : FixedBinaryWord A => A)) header.targets
  (⟨header.region,header.fixed,targets.1⟩,targets.2 + GeneralPaperLastRegionSelection.price S A header.region +
    GeneralPaperEncodedScalarStorage.natBits header.fixed + 64 * (S + A + 1))

theorem copy_header_data (S A : ℕ) (header : Header A) : (copyHeader S A header).1 = header := by
  dsimp only [copyHeader]
  rw [GeneralPaperReferenceCopy.list_data S S _ (fun _ => rfl)]


def appendHeaders (S A : ℕ) : List (Header A) → List (Header A) → List (Header A) × ℕ
  | [],rest => (rest,64 * (S + A + 1))
  | header :: headers,rest =>
    let actual := copyHeader S A header
    let later := appendHeaders S A headers rest
    (actual.1 :: later.1,actual.2 + later.2 + 64 * (S + A + 1))

def appendCells (S A : ℕ) : List (Cell A) → List (Cell A) → List (Cell A) × ℕ
  | [],rest => (rest,64 * (S + A + 1))
  | cell :: cells,rest =>
    let later := appendCells S A cells rest
    (cell :: later.1,later.2 + GeneralPaperLastRegionSelection.price S A cell.region +
      GeneralPaperRetainedScalarValue.encode cell.value + 64 * (S + A + 1))

theorem append_headers_data (S A : ℕ) (first rest : List (Header A)) : (appendHeaders S A first rest).1 = first ++ rest := by
  induction first with
  | nil => rfl
  | cons header headers ih => simp only [appendHeaders,copy_header_data,ih,List.cons_append]

theorem append_cells_data (S A : ℕ) (first rest : List (Cell A)) : (appendCells S A first rest).1 = first ++ rest := by
  induction first with
  | nil => rfl
  | cons cell cells ih => simp only [appendCells,ih,List.cons_append]

theorem append_headers_work (S A : ℕ) (first rest : List (Header A)) :
    (appendHeaders S A first rest).2 = (first.map (fun header => (copyHeader S A header).2)).sum +
      (first.length + 1) * (64 * (S + A + 1)) := by
  induction first with
  | nil => simp only [appendHeaders,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_add,Nat.one_mul]
  | cons header headers ih => simp only [appendHeaders,ih,List.map_cons,List.sum_cons,List.length_cons]; ring

theorem append_cells_work (S A : ℕ) (first rest : List (Cell A)) :
    (appendCells S A first rest).2 =
      (first.map (fun cell => GeneralPaperLastRegionSelection.price S A cell.region + GeneralPaperRetainedScalarValue.encode cell.value)).sum +
      (first.length + 1) * (64 * (S + A + 1)) := by
  induction first with
  | nil => simp only [appendCells,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_add,Nat.one_mul]
  | cons cell cells ih => simp only [appendCells,ih,List.map_cons,List.sum_cons,List.length_cons]; ring

structure Body (A : ℕ) where
  roots : List (Region A)
  headers : List (Header A)
  cells : List (Cell A)

def prepend (S A : ℕ) (directory : Directory A) (tail : Body A) : Body A × ℕ :=
  let headers := appendHeaders S A directory.headers tail.headers
  let cells := appendCells S A directory.cells tail.cells
  (⟨directory.root :: tail.roots,headers.1,cells.1⟩,
    headers.2 + cells.2 + GeneralPaperLastRegionSelection.price S A directory.root + 64 * (S + A + 1))

theorem prepend_roots (S A : ℕ) (directory : Directory A) (tail : Body A) :
    (prepend S A directory tail).1.roots = directory.root :: tail.roots := rfl

theorem prepend_headers (S A : ℕ) (directory : Directory A) (tail : Body A) :
    (prepend S A directory tail).1.headers = directory.headers ++ tail.headers := by simp only [prepend,append_headers_data]

theorem prepend_cells (S A : ℕ) (directory : Directory A) (tail : Body A) :
    (prepend S A directory tail).1.cells = directory.cells ++ tail.cells := by simp only [prepend,append_cells_data]

end Blotto.GeneralPaperFieldDirectory
