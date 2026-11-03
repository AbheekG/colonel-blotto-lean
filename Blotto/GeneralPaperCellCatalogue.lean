import Blotto.GeneralPaperLeastValidResource

/-! Execute one least-valid lookup per prepared cell and retain optional
typed code/threshold payloads in a native array. This stage does not sort or
enumerate the code alphabet. Absence, minimum resource and all payload
validity are derived from the actual lookup, with its declared source work.
-/
namespace Blotto.GeneralPaperCellCatalogue
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode GeneralPaperCodeMinimumScan
open GeneralPaperEpochCellInstructions
set_option autoImplicit false
set_option maxHeartbeats 3500000

def build {n : ℕ} (a : Alphabet) (response : Bool) (cells : Cells n) : FixedArrayTable n (Option Entry) × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun r =>
    let cell := cells.read r
    let found := GeneralPaperLeastValidCell.run a response cell.1 cell.2
    (found.selected,found.work+12))

theorem read_build {n : ℕ} (a : Alphabet) (response : Bool) (cells : Cells n) (r : Fin n) :
    (build a response cells).1.read r=(GeneralPaperLeastValidCell.run a response (cells.read r).1 (cells.read r).2).selected := by
  rw [build,PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]

theorem sound {n : ℕ} (a : Alphabet) (response : Bool) (cells : Cells n) (r : Fin n) (entry : Entry)
    (hSome : (build a response cells).1.read r=some entry) :
    Contains cells r entry.cost ∧ (decode a response entry.cost).choice=some entry.predecessor := by
  rw [read_build] at hSome
  have he := GeneralPaperLeastValidCell.run_sound a response (cells.read r).1 (cells.read r).2 entry hSome
  exact ⟨⟨he.1,he.2.1⟩,he.2.2⟩

theorem none_iff {n : ℕ} (a : Alphabet) (response : Bool) (cells : Cells n) (r : Fin n) :
    (build a response cells).1.read r=none ↔ ∀ code, Contains cells r code → ¬Valid a response code := by
  rw [read_build,GeneralPaperLeastValidCell.run_none_iff]
  constructor
  · intro h code hc
    exact h code hc.1 hc.2
  · intro h code hLo hHi
    exact h code ⟨hLo,hHi⟩

theorem dominates {n : ℕ} (a : Alphabet) (response : Bool) (cells : Cells n) (r : Fin n) (entry : Entry)
    (hSome : (build a response cells).1.read r=some entry) (code : ℕ) (choice : Choice)
    (hCell : Contains cells r code) (hDecode : (decode a response code).choice=some choice) :
    entry.predecessor.tag≤choice.tag := by
  rw [read_build] at hSome
  exact GeneralPaperLeastValidResource.cell_domination a response (cells.read r).1 (cells.read r).2 entry hSome
    code choice hCell.1 hCell.2 hDecode

theorem covers_valid {n : ℕ} (a : Alphabet) (response : Bool) (cells : Cells n) (r : Fin n)
    (code : ℕ) (choice : Choice) (hCell : Contains cells r code)
    (hDecode : (decode a response code).choice=some choice) :
    ∃ entry, (build a response cells).1.read r=some entry ∧ Contains cells r entry.cost ∧ entry.predecessor.tag≤choice.tag := by
  cases hs : (build a response cells).1.read r with
  | none =>
    exact ((none_iff a response cells r).mp hs code hCell
      (GeneralPaperCodeDecodeSound.decode_valid a response code choice hDecode)).elim
  | some entry =>
    exact ⟨entry,rfl,(sound a response cells r entry hs).1,dominates a response cells r entry hs code choice hCell hDecode⟩

theorem build_work {n : ℕ} (a : Alphabet) (response : Bool) (cells : Cells n) :
    (build a response cells).2≤n*(934*a.lambda+2772)+18 := by
  rw [build,PaperIndexedArrayConstruction.run_work,GeneralPaperEpochLevelArray.overhead]
  have he : (∑ r : Fin n, ((GeneralPaperLeastValidCell.run a response (cells.read r).1 (cells.read r).2).work+12))≤
      n*(934*a.lambda+2730) := by
    calc
      _ ≤ ∑ _r : Fin n, (934*a.lambda+2730) := by
        apply Finset.sum_le_sum
        intro r _
        have hw := GeneralPaperLeastValidCell.run_work a response (cells.read r).1 (cells.read r).2
        omega
      _ = _ := by simp
  dsimp only
  nlinarith only [he]

end Blotto.GeneralPaperCellCatalogue
