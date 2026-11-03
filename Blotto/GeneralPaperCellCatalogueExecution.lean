import Blotto.GeneralPaperLeastValidCellPrice

/-! One native cell-catalogue fill retains selected entries and accumulates
the existing lookup-work annotation. Fusing callback/loop annotation constants
does not add a traversal. Every cell lookup is called exactly once.
-/
namespace Blotto.GeneralPaperCellCatalogueExecution
open GeneralPaperCodeAlphabet
open GeneralPaperCodeMinimumScan (Entry)
open GeneralPaperDecodeBucketExecution (primitive)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def slot (bits : Bool) (W count : ℕ) : ℕ :=
  if bits then GeneralPaperSummaryArrayExecution.arrayWord W count else W

def fill {n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (cells : GeneralPaperEpochCellInstructions.Cells n) :
    (count : ℕ) → count≤n → (Array (Option Entry) × ℕ) × ℕ
  | 0,_ => ((#[],18),PaperIndexedArrayConstruction.initialWork index (slot bits W n) n+64*W)
  | count+1,hCount =>
    let earlier := fill bits index model W a response cells count (by omega)
    let cell := cells.read ⟨count,by omega⟩
    let found := GeneralPaperLeastValidCellExecution.run bits model W a response cell.1 cell.2
    ((earlier.1.1.push found.1.selected,earlier.1.2+found.1.work+54),
      earlier.2+found.2+PaperIndexedArrayConstruction.stepWork index (slot bits W n) count+48*W+
      GeneralPaperNaturalPrimitivePrice.binary (primitive bits model) (fun a b => a+b) earlier.1.2 found.1.work+
      GeneralPaperNaturalPrimitivePrice.binary (primitive bits model) (fun a b => a+b) (earlier.1.2+found.1.work) 54)

theorem fill_size {n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (cells : GeneralPaperEpochCellInstructions.Cells n) (count : ℕ) (hCount : count≤n) :
    (fill bits index model W a response cells count hCount).1.1.size=count := by
  induction count with
  | zero => rfl
  | succ count ih => rw [fill]; dsimp only; rw [Array.size_push,ih]

def run {n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (cells : GeneralPaperEpochCellInstructions.Cells n) :
    (FixedArrayTable n (Option Entry) × ℕ) × ℕ :=
  let result := fill bits index model W a response cells n (Nat.le_refl _)
  ((⟨result.1.1,fill_size bits index model W a response cells n (Nat.le_refl _)⟩,result.1.2),result.2+64*W)

end Blotto.GeneralPaperCellCatalogueExecution
