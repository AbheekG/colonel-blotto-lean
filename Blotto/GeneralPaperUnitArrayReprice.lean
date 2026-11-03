import Blotto.GeneralPaperBasisArrayPrice

/-! Exact conversion of older indexed constructors with their separate
index primitive disabled to unit-price index operations. Data are identical;
the difference is two initial operations and eight per stored entry.
-/
namespace Blotto.GeneralPaperUnitArrayReprice
open scoped BigOperators
set_option autoImplicit false

theorem overhead (W count k : ℕ) :
    PaperIndexedArrayConstruction.overhead (fun _ => 1) W count k=
      PaperIndexedArrayConstruction.overhead (fun _ => 0) W count k+8*k+2 := by
  induction k with
  | zero => simp only [PaperIndexedArrayConstruction.overhead,PaperIndexedArrayConstruction.initialWork]
  | succ k ih =>
    simp only [PaperIndexedArrayConstruction.overhead,PaperIndexedArrayConstruction.stepWork,ih]
    omega

theorem work {α : Type*} {n : ℕ} (W : ℕ) (callback : Fin n → α × ℕ) :
    (PaperIndexedArrayConstruction.run (fun _ => 1) W callback).2=
      (PaperIndexedArrayConstruction.run (fun _ => 0) W callback).2+8*n+2 := by
  rw [PaperIndexedArrayConstruction.run_work,PaperIndexedArrayConstruction.run_work,overhead]
  omega

end Blotto.GeneralPaperUnitArrayReprice
