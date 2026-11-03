import Blotto.GeneralPaperCellCatalogueExecution

/-! The optional-entry array and native lookup-work field agree together.
Array size transports are erased, with no copy or annotation-sum traversal.
-/
namespace Blotto.GeneralPaperCellCatalogueData
open GeneralPaperCodeAlphabet GeneralPaperCellCatalogueExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem fill_data {n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (cells : GeneralPaperEpochCellInstructions.Cells n) (count : ℕ) (hCount : count≤n) :
    (fill bits index model W a response cells count hCount).1=
      PaperIndexedArrayConstruction.fill (fun _ => 1) 1 (fun r : Fin n =>
        let cell := cells.read r
        let found := GeneralPaperLeastValidCell.run a response cell.1 cell.2
        (found.selected,found.work+12)) count hCount := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [fill,PaperIndexedArrayConstruction.fill]
    dsimp only
    rw [ih,GeneralPaperLeastValidCellExecution.data]
    dsimp only [PaperIndexedArrayConstruction.stepWork]
    congr 1

theorem data {n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (cells : GeneralPaperEpochCellInstructions.Cells n) :
    (run bits index model W a response cells).1=GeneralPaperCellCatalogue.build a response cells := by
  unfold run GeneralPaperCellCatalogue.build PaperIndexedArrayConstruction.run
  dsimp only
  have h := fill_data bits index model W a response cells n (Nat.le_refl _)
  simp only [Prod.mk.injEq,FixedArrayTable.mk.injEq]
  exact ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩

theorem same_data {n : ℕ} (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (cells : GeneralPaperEpochCellInstructions.Cells n) :
    (run true (fun w => w) model W a response cells).1=
      (run false (fun _ => 1) model 1 a response cells).1 := by
  rw [data,data]

theorem sound {n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (cells : GeneralPaperEpochCellInstructions.Cells n)
    (r : Fin n) (entry : GeneralPaperCodeMinimumScan.Entry)
    (hSome : (run bits index model W a response cells).1.1.read r=some entry) :
    GeneralPaperEpochCellInstructions.Contains cells r entry.cost ∧
      (GeneralPaperCodeDecode.decode a response entry.cost).choice=some entry.predecessor := by
  rw [data] at hSome
  exact GeneralPaperCellCatalogue.sound a response cells r entry hSome

theorem none_iff {n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (cells : GeneralPaperEpochCellInstructions.Cells n) (r : Fin n) :
    (run bits index model W a response cells).1.1.read r=none ↔
      ∀ code, GeneralPaperEpochCellInstructions.Contains cells r code → ¬Valid a response code := by
  rw [data]
  exact GeneralPaperCellCatalogue.none_iff a response cells r

theorem dominates {n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (cells : GeneralPaperEpochCellInstructions.Cells n)
    (r : Fin n) (entry : GeneralPaperCodeMinimumScan.Entry)
    (hSome : (run bits index model W a response cells).1.1.read r=some entry)
    (code : ℕ) (choice : Choice) (hCell : GeneralPaperEpochCellInstructions.Contains cells r code)
    (hDecode : (GeneralPaperCodeDecode.decode a response code).choice=some choice) :
    entry.predecessor.tag≤choice.tag := by
  rw [data] at hSome
  exact GeneralPaperCellCatalogue.dominates a response cells r entry hSome code choice hCell hDecode

theorem covers_valid {n : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (a : Alphabet) (response : Bool) (cells : GeneralPaperEpochCellInstructions.Cells n) (r : Fin n)
    (code : ℕ) (choice : Choice) (hCell : GeneralPaperEpochCellInstructions.Contains cells r code)
    (hDecode : (GeneralPaperCodeDecode.decode a response code).choice=some choice) :
    ∃ entry, (run bits index model W a response cells).1.1.read r=some entry ∧
      GeneralPaperEpochCellInstructions.Contains cells r entry.cost ∧ entry.predecessor.tag≤choice.tag := by
  rw [data]
  exact GeneralPaperCellCatalogue.covers_valid a response cells r code choice hCell hDecode

end Blotto.GeneralPaperCellCatalogueData
