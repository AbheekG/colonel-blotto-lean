import Blotto.PlayerSpecificAcceptance
import Mathlib.Algebra.Polynomial.Roots

/-! Actual degree-at-most-three polynomial and finite real-root semantics.
The root list here specifies the paper's augmented real-RAM primitive. It
is explicitly noncomputable and is not the finite-bit root implementation. -/
namespace Blotto.PlayerSpecificPolynomial
open PlayerSpecificCubic
set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def polynomial {𝕂 : Type*} [Field 𝕂] (c : Coefficients 𝕂) (b : 𝕂) : Polynomial 𝕂 :=
  Polynomial.C c.B1*Polynomial.X^3-Polynomial.C (b*c.A1)*Polynomial.X^2+
    Polynomial.C c.B2*Polynomial.X-Polynomial.C (b*c.A2)

theorem eval {𝕂 : Type*} [Field 𝕂] (c : Coefficients 𝕂) (b gamma : 𝕂) :
    (polynomial c b).eval gamma=cubic c b gamma := by simp [polynomial,cubic]

theorem coefficient_three {𝕂 : Type*} [Field 𝕂] (c : Coefficients 𝕂) (b : 𝕂) :
    (polynomial c b).coeff 3=c.B1 := by
  simp only [polynomial,Polynomial.coeff_sub,Polynomial.coeff_add,
    Polynomial.coeff_C_mul_X_pow,Polynomial.coeff_C_mul_X,Polynomial.coeff_C]
  norm_num

theorem coefficient_one {𝕂 : Type*} [Field 𝕂] (c : Coefficients 𝕂) (b : 𝕂) :
    (polynomial c b).coeff 1=c.B2 := by
  simp only [polynomial,Polynomial.coeff_sub,Polynomial.coeff_add,
    Polynomial.coeff_C_mul_X_pow,Polynomial.coeff_C_mul_X,Polynomial.coeff_C]
  norm_num

theorem degree_le {𝕂 : Type*} [Field 𝕂] (c : Coefficients 𝕂) (b : 𝕂) :
    (polynomial c b).natDegree≤3 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro N hN
  have h3 : N≠3 := by omega
  have h2 : N≠2 := by omega
  have h1 : N≠1 := by omega
  have h0 : N≠0 := by omega
  simp only [polynomial,Polynomial.coeff_sub,Polynomial.coeff_add,
    Polynomial.coeff_C_mul_X_pow,Polynomial.coeff_C_mul_X,Polynomial.coeff_C]
  simp [h3,h2,h1,h0]

theorem nonzero {𝕂 : Type*} [Field 𝕂] [LinearOrder 𝕂] [IsStrictOrderedRing 𝕂] {n : ℕ}
    (v w : Fin n → 𝕂) (high : Fin n → Bool) (b : 𝕂) (hn : 0<n)
    (hv : ∀ j,0<v j) (hw : ∀ j,0<w j) : polynomial (coefficients v w high) b≠0 := by
  intro hz
  rcases PlayerSpecificCandidate.nonzero_coefficients v w high hn hv hw with h | h
  · have he := congrArg (fun p : Polynomial 𝕂 => p.coeff 3) hz
    rw [coefficient_three,Polynomial.coeff_zero] at he
    exact h.ne' he
  · have he := congrArg (fun p : Polynomial 𝕂 => p.coeff 1) hz
    rw [coefficient_one,Polynomial.coeff_zero] at he
    exact h.ne' he

noncomputable def roots (c : Coefficients ℝ) (b : ℝ) : List ℝ :=
  (polynomial c b).roots.toFinset.toList

theorem root_count (c : Coefficients ℝ) (b : ℝ) : (roots c b).length≤3 := by
  classical
  dsimp only [roots]
  rw [Finset.length_toList]
  exact (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans (degree_le c b))

theorem root_membership (c : Coefficients ℝ) (b gamma : ℝ) (hc : polynomial c b≠0) :
    gamma∈roots c b ↔ cubic c b gamma=0 := by
  classical
  simp only [roots,Finset.mem_toList,Multiset.mem_toFinset,Polynomial.mem_roots hc,Polynomial.IsRoot,eval]

theorem actual_root_membership {n : ℕ} (v w : Fin n → ℝ) (high : Fin n → Bool) (b gamma : ℝ)
    (hn : 0<n) (hv : ∀ j,0<v j) (hw : ∀ j,0<w j) :
    gamma∈roots (coefficients v w high) b ↔ cubic (coefficients v w high) b gamma=0 :=
  root_membership _ b gamma (nonzero v w high b hn hv hw)

end Blotto.PlayerSpecificPolynomial
