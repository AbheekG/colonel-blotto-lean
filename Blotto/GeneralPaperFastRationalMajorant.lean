import Blotto.GeneralPaperSelectorRefinedSourcePrice

/-! A valid explicit logarithmic Rat model dominates any model satisfying
the paper's Growth convention. The harmless coefficient increase C -> C+1
keeps the majorant valid even at C=0. Only closed prices are compared; no
algorithm is re-executed with a substituted primitive implementation. -/
namespace Blotto.GeneralPaperFastRationalMajorant
open GeneralPaperFastRationalModel
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem coefficient_mono (C D d w : ℕ) (h : C≤D) : charge C d w≤charge D d w :=
  Nat.mul_le_mul_right _ (Nat.mul_le_mul_right w h)

def model (C d : ℕ) : RationalCostModel where
  rat := charge (C+1) d
  monotone := charge_monotone (C+1) d
  word_le := fun w => ((fast d).word_le w).trans (coefficient_mono 1 (C+1) d w (by omega))
  superadditive := charge_superadditive (C+1) d

theorem price (C d w : ℕ) : (model C d).rat w=charge (C+1) d w := rfl

theorem growth (C d : ℕ) : Growth (model C d) (C+1) d := fun _ => Nat.le_refl _

theorem dominates {actual : RationalCostModel} {C d : ℕ} (hg : Growth actual C d) (w : ℕ) :
    actual.rat w≤(model C d).rat w :=
  (hg w).trans (coefficient_mono C (C+1) d w (Nat.le_succ _))

end Blotto.GeneralPaperFastRationalMajorant
