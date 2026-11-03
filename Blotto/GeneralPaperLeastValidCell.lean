import Blotto.GeneralPaperLeastValidSpec

/-! The half-open cell interface required by epoch catalogues. A guard
handles empty cells before converting the upper endpoint to an inclusive
bound, so natural subtraction never turns [0,0) into a zero option.
-/
namespace Blotto.GeneralPaperLeastValidCell
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode
open GeneralPaperCodeMinimumScan
open GeneralPaperOrderedMinimum (Best)
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 2048

def run (a : Alphabet) (response : Bool) (lo hi : ℕ) : GeneralPaperCodeMinimumScan.Result :=
  if lo<hi then
    let found := GeneralPaperLeastValid.run a response lo (hi-1)
    ⟨found.selected,found.work+16⟩
  else ⟨none,16⟩

def Possible (a : Alphabet) (response : Bool) (lo hi : ℕ) (entry : Entry) : Prop :=
  lo≤entry.cost ∧ entry.cost<hi ∧ (decode a response entry.cost).choice=some entry.predecessor

theorem run_best (a : Alphabet) (response : Bool) (lo hi : ℕ) :
    Best (Possible a response lo hi) (run a response lo hi).selected := by
  dsimp only [run]
  split
  · rename_i hRange
    exact best_congr _ _ _ (by
      intro entry
      unfold GeneralPaperCodeMinimumScan.Possible Possible
      constructor <;> rintro ⟨hLo,hHi,hDecode⟩ <;> exact ⟨hLo,by omega,hDecode⟩)
      (GeneralPaperLeastValid.run_best a response lo (hi-1))
  · rename_i hRange
    intro entry he
    have hLo := he.1
    have hHi := he.2.1
    omega

theorem run_sound (a : Alphabet) (response : Bool) (lo hi : ℕ) (entry : Entry)
    (hSome : (run a response lo hi).selected=some entry) : Possible a response lo hi entry := by
  have hb := run_best a response lo hi
  rw [hSome] at hb
  exact hb.1

theorem run_minimal (a : Alphabet) (response : Bool) (lo hi : ℕ) (entry : Entry)
    (hSome : (run a response lo hi).selected=some entry) (other : Entry)
    (hOther : Possible a response lo hi other) : entry.cost≤other.cost := by
  have hb := run_best a response lo hi
  rw [hSome] at hb
  exact hb.2 other hOther

theorem run_none_iff (a : Alphabet) (response : Bool) (lo hi : ℕ) :
    (run a response lo hi).selected=none ↔ ∀ code, lo≤code → code<hi → ¬Valid a response code := by
  dsimp only [run]
  split
  · rename_i hRange
    rw [GeneralPaperLeastValidSpec.run_none_iff]
    constructor <;> intro h code hLo hHi <;> exact h code hLo (by omega)
  · rename_i hRange
    simp only [true_iff]
    intro code hLo hHi _
    omega

theorem empty_none (a : Alphabet) (response : Bool) (lo hi : ℕ) (hEmpty : hi≤lo) :
    (run a response lo hi).selected=none := by
  simp only [run,not_lt.mpr hEmpty,ite_false]

theorem run_work (a : Alphabet) (response : Bool) (lo hi : ℕ) :
    (run a response lo hi).work≤934*a.lambda+2718 := by
  dsimp only [run]
  split
  · have he := GeneralPaperLeastValid.run_work a response lo (hi-1)
    dsimp only
    omega
  · dsimp only
    omega

end Blotto.GeneralPaperLeastValidCell
