import Blotto.GeneralPaperInitializerActualRoots

/-! Rational field values from the actual source's native integer weights.
The strict-score phase reads these same values; their real casts equal the
canonical normalized values used in the source-security proof exactly.
-/
namespace Blotto.GeneralPaperNativeRationalValues
open scoped BigOperators
set_option autoImplicit false

def selector {m : ℕ} (Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) : RationalFieldSelector m where
  weight := fun j => (weights.read j:ℚ)/Qv
  positive := fun j => div_pos (by exact_mod_cast hp j) (by exact_mod_cast hQv)
  sum_one := by
    rw [←Finset.sum_div]
    have he : (∑ j,(weights.read j:ℚ))=(Qv:ℚ) := by exact_mod_cast hs
    rw [he,div_self (by exact_mod_cast hQv.ne')]

theorem real_weight {m : ℕ} (Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (j : Fin m) :
    ((selector Qv hQv weights hp hs).values).weight j=
      (GeneralPaperCatalogueCanonicalGap.normalizedValues Qv hQv weights hp hs).weight j := by
  change (((weights.read j:ℚ)/Qv:ℚ):ℝ)=(weights.read j:ℝ)/Qv
  simp only [Rat.cast_div,Rat.cast_natCast]

end Blotto.GeneralPaperNativeRationalValues
