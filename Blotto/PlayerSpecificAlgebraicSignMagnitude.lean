import Blotto.PlayerSpecificHornerLipschitz

/-! Computed exact nonzero-value and variation bounds for sign decisions.
Both integers are evaluated from actual coefficients/certificates/enclosure. -/
namespace Blotto.PlayerSpecificAlgebraicSignMagnitude
open PlayerSpecificDensePolynomial PlayerSpecificSturmVariations PlayerSpecificRationalMagnitude
set_option autoImplicit false
set_option maxHeartbeats 2000000

def gapDenominator (m a : Data) (M : ℕ) : ℕ :=
  let certificate:=PlayerSpecificAlgebraicBezout.right m a
  2^inputHeight certificate*(1+M)^certificate.length
def lipschitz (a : Data) (M : ℕ) : ℕ := 1+a.length*2^inputHeight a*(1+M)^a.length

theorem gap_positive (m a : Data) (M : ℕ) : 0<gapDenominator m a M :=
  Nat.mul_pos (Nat.two_pow_pos _) (Nat.pow_pos (by omega))
theorem lipschitz_positive (a : Data) (M : ℕ) : 0<lipschitz a M := by unfold lipschitz; omega

theorem gap (m a : Data) (hirr : Irreducible (semantics m)) (ha : semantics a≠0)
    (hdeg : (semantics a).natDegree<(semantics m).natDegree) (M : ℕ) (x : ℝ)
    (hx : realEvaluate m x=0) (hM : |x| ≤ (M:ℝ)) :
    (1:ℝ)/(gapDenominator m a M:ℝ)≤|realEvaluate a x| := by
  have hi:=congrArg abs (PlayerSpecificAlgebraicBezout.real_identity m a hirr ha hdeg x hx)
  rw [abs_mul,abs_one] at hi
  have hb:=PlayerSpecificEvaluationMagnitude.encoded_bound (PlayerSpecificAlgebraicBezout.right m a) (M:ℝ) x (Nat.cast_nonneg _) hM
  rw [PlayerSpecificSquarefreeAlgorithm.real_evaluate] at hb
  have hbound : |realEvaluate (PlayerSpecificAlgebraicBezout.right m a) x| ≤ (gapDenominator m a M:ℝ) := by
    simpa only [gapDenominator,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using hb
  have hp:=mul_le_mul_of_nonneg_left hbound (abs_nonneg (realEvaluate a x))
  rw [hi] at hp
  exact (div_le_iff₀ (by exact_mod_cast gap_positive m a M)).mpr hp

theorem variation (a : Data) (M : ℕ) (x y : ℝ) (hx : |x| ≤ (M:ℝ)) (hy : |y| ≤ (M:ℝ)) :
    |realEvaluate a x-realEvaluate a y| ≤ (lipschitz a M:ℝ)*|x-y| := by
  have h:=PlayerSpecificHornerLipschitz.encoded a (M:ℝ) x y (Nat.cast_nonneg _) hx hy
  have hm : (a.length:ℝ)*(2:ℝ)^inputHeight a*(1+(M:ℝ))^a.length≤(lipschitz a M:ℝ) := by
    simp only [lipschitz,Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    linarith
  exact h.trans (mul_le_mul_of_nonneg_right hm (abs_nonneg _))

end Blotto.PlayerSpecificAlgebraicSignMagnitude
