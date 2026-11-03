import Blotto.PlayerSpecificEvaluationMagnitude
import Blotto.PlayerSpecificSquarefreeCoprime

/-! A separation bound calculated from the input and its actual extended
Euclidean certificate. All bound data is rational/integer and executable.
Polynomial input-height bounds for this data are proved separately. -/
namespace Blotto.PlayerSpecificRootSeparation
open PlayerSpecificDensePolynomial PlayerSpecificRationalMagnitude PlayerSpecificRootMagnitude
open PlayerSpecificSquarefreeAlgorithm PlayerSpecificSquarefreeCoprime PlayerSpecificEvaluationMagnitude
set_option autoImplicit false
set_option maxHeartbeats 5000000

def bezoutBound (p : Data) : ℕ :=
  2^inputHeight (unitRight p)*(1+rootBound p)^(unitRight p).length

def derivativeBound (p : Data) : ℕ :=
  2^inputHeight (PlayerSpecificSquarefreeAlgorithm.run p)*(1+3*rootBound p)

def separationDenominator (p : Data) : ℕ := derivativeBound p*bezoutBound p

theorem bezoutBound_pos (p : Data) : 0<bezoutBound p :=
  Nat.mul_pos (Nat.two_pow_pos _) (Nat.pow_pos (by omega))

theorem derivativeBound_pos (p : Data) : 0<derivativeBound p :=
  Nat.mul_pos (Nat.two_pow_pos _) (by omega)

theorem separationDenominator_pos (p : Data) : 0<separationDenominator p :=
  Nat.mul_pos (derivativeBound_pos p) (bezoutBound_pos p)

theorem squarefree_degree (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    (realPolynomial (PlayerSpecificSquarefreeAlgorithm.run p)).natDegree≤3 := by
  rw [realPolynomial,Polynomial.natDegree_map]
  have hd : semantics (PlayerSpecificSquarefreeAlgorithm.run p)∣semantics p :=
    ⟨semantics (gcdDerivative p),by rw [decomposition p]; ring⟩
  have h := (Polynomial.natDegree_le_of_dvd hd hp).trans (PlayerSpecificPolynomialNormalization.degree_le p)
  omega

theorem bezout_at_root (p : Data) (hp : semantics p≠0) (r : ℝ)
    (hr : (realPolynomial (PlayerSpecificSquarefreeAlgorithm.run p)).eval r=0) :
    (realPolynomial (PlayerSpecificSquarefreeAlgorithm.run p)).derivative.eval r*
      (realPolynomial (unitRight p)).eval r=1 := by
  have hi := congrArg (fun q : Polynomial ℚ => (q.map (Rat.castHom ℝ)).eval r) (unit_identity p hp)
  simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_one,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_one,← Polynomial.derivative_map] at hi
  change (realPolynomial (PlayerSpecificSquarefreeAlgorithm.run p)).eval r*(realPolynomial (unitLeft p)).eval r+
    (realPolynomial (PlayerSpecificSquarefreeAlgorithm.run p)).derivative.eval r*(realPolynomial (unitRight p)).eval r=1 at hi
  simpa only [hr,zero_mul,zero_add] using hi

theorem separated (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    PlayerSpecificIsolationBounds.Separated p ((1:ℝ)/(separationDenominator p:ℝ)) := by
  intro r s hr hs hne
  have hsr : (realPolynomial (PlayerSpecificSquarefreeAlgorithm.run p)).eval r=0 := by
    rw [real_evaluate,evaluated_roots_preserved p hp r]; exact hr
  have hss : (realPolynomial (PlayerSpecificSquarefreeAlgorithm.run p)).eval s=0 := by
    rw [real_evaluate,evaluated_roots_preserved p hp s]; exact hs
  have hrM := (root_lt p hp r hr).le
  have hsM := (root_lt p hp s hs).le
  have hM : (0:ℝ)≤(rootBound p:ℝ) := Nat.cast_nonneg _
  have hcoef (j : ℕ) : |(realPolynomial (PlayerSpecificSquarefreeAlgorithm.run p)).coeff j| ≤
      (2:ℝ)^inputHeight (PlayerSpecificSquarefreeAlgorithm.run p) := by
    rw [real_coefficient]
    exact (real_upper _ _ (coefficient_height _ j)).le
  have hd := derivative_distance _ (squarefree_degree p hp hlen) r s
    ((2:ℝ)^inputHeight (PlayerSpecificSquarefreeAlgorithm.run p)) (rootBound p:ℝ)
    hsr hss hne (pow_nonneg (by norm_num) _) hM (hcoef 2) (hcoef 3) hrM hsM
  have hd' : |(realPolynomial (PlayerSpecificSquarefreeAlgorithm.run p)).derivative.eval r| ≤
      |r-s| * (derivativeBound p:ℝ) := by
    simpa only [derivativeBound,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat] using hd
  have hb : |(realPolynomial (unitRight p)).eval r| ≤ (bezoutBound p:ℝ) := by
    simpa only [bezoutBound,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_pow,Nat.cast_ofNat] using
      encoded_bound (unitRight p) (rootBound p:ℝ) r hM hrM
  have hi := congrArg abs (bezout_at_root p hp r hsr)
  rw [abs_mul,abs_one] at hi
  have hprod := mul_le_mul hd' hb (abs_nonneg _) (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
  have hone : (1:ℝ)≤|r-s| * (separationDenominator p:ℝ) := by
    rw [hi] at hprod
    simpa only [separationDenominator,Nat.cast_mul,mul_assoc] using hprod
  have hpos : (0:ℝ)<(separationDenominator p:ℝ) := by exact_mod_cast separationDenominator_pos p
  exact (div_le_iff₀ hpos).mpr hone

end Blotto.PlayerSpecificRootSeparation
