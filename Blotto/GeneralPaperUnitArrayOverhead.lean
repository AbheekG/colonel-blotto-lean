import Blotto.GeneralPaperParametricStageBits

/-! Unit arithmetic prices for the paper's indexed reference constructor.
The index primitive is constant-price in the real-RAM model; it requires
no input-encoding-length query or bit-word capacity premise.
-/
namespace Blotto.GeneralPaperUnitArrayOverhead
set_option autoImplicit false

theorem overhead (W count k : ℕ) :
    PaperIndexedArrayConstruction.overhead (fun _ => 1) W count k≤(k+1)*(6*W+36) := by
  induction k with
  | zero =>
    simp only [PaperIndexedArrayConstruction.overhead,PaperIndexedArrayConstruction.initialWork]
    omega
  | succ k ih =>
    simp only [PaperIndexedArrayConstruction.overhead,PaperIndexedArrayConstruction.stepWork]
    nlinarith only [ih]

theorem score_overhead (S : ℕ) :
    PaperIndexedArrayConstruction.overhead (fun _ => 1) 1 (S+1) (S+1)≤88*(S+1) := by
  have hh := overhead 1 (S+1) (S+1)
  omega

end Blotto.GeneralPaperUnitArrayOverhead
