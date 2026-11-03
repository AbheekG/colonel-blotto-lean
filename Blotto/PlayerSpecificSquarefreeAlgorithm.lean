import Blotto.PlayerSpecificSquarefreeReduction

/-! The actual rational derivative-GCD quotient preserves every real root,
including irrational roots, and every resulting real root is simple. The
extension-of-scalars proof derives a Bezout certificate from the already
checked computed GCD; it supplies no runtime algebraic-number oracle. -/
namespace Blotto.PlayerSpecificSquarefreeAlgorithm
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSquarefreeReduction
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem bezout {𝕂 : Type*} [Field 𝕂] (p q g : Polynomial 𝕂) (hg : CommonDivisors p q g) :
    ∃ a b : Polynomial 𝕂,g=p*a+q*b := by
  classical
  have hd : EuclideanDomain.gcd p q∣g := (hg _).mpr
    ⟨EuclideanDomain.gcd_dvd_left _ _,EuclideanDomain.gcd_dvd_right _ _⟩
  rcases hd with ⟨u,hu⟩
  refine ⟨EuclideanDomain.gcdA p q*u,EuclideanDomain.gcdB p q*u,?_⟩
  rw [hu,EuclideanDomain.gcd_eq_gcd_ab]
  ring

theorem common_map {𝕂 𝕁 : Type*} [Field 𝕂] [Field 𝕁] (p q g : Polynomial 𝕂)
    (hg : CommonDivisors p q g) (f : 𝕂 →+* 𝕁) :
    CommonDivisors (p.map f) (q.map f) (g.map f) := by
  rcases bezout p q g hg with ⟨a,b,hbez⟩
  have hd := (hg g).mp dvd_rfl
  intro r
  constructor
  · intro hr
    exact ⟨hr.trans (Polynomial.map_dvd f hd.1),hr.trans (Polynomial.map_dvd f hd.2)⟩
  · rintro ⟨hp,hq⟩
    rw [hbez,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_mul]
    exact dvd_add (hp.mul_right _) (hq.mul_right _)

def gcdDerivative (p : Data) : Data := PlayerSpecificPolynomialGCD.run p (derivative p)
def run (p : Data) : Data := (PlayerSpecificPolynomialDivision.run p (gcdDerivative p)).1

theorem common (p : Data) : CommonDivisors (semantics p) (semantics p).derivative (semantics (gcdDerivative p)) := by
  intro r
  rw [← derivative_semantics]
  exact PlayerSpecificPolynomialGCD.run_common_divisors p (derivative p) r

theorem decomposition (p : Data) : semantics p=semantics (gcdDerivative p)*semantics (run p) := by
  have hd := ((common p) (semantics (gcdDerivative p))).mp dvd_rfl
  have hr := PlayerSpecificPolynomialDivision.reconstruction p (gcdDerivative p)
  rw [← (PlayerSpecificPolynomialDivision.refines p (gcdDerivative p)).2,
    EuclideanDomain.mod_eq_zero.mpr hd.1,add_zero] at hr
  exact hr.symm

theorem normalized (p : Data) : Normalized (run p) := PlayerSpecificPolynomialDivision.quotient_normalized _ _

noncomputable def realPolynomial (p : Data) : Polynomial ℝ := (semantics p).map (Rat.castHom ℝ)

theorem real_nonzero (p : Data) (hp : semantics p≠0) : realPolynomial p≠0 := by
  intro hz
  exact hp ((Polynomial.map_eq_zero (Rat.castHom ℝ)).mp hz)

theorem real_common (p : Data) :
    CommonDivisors (realPolynomial p) (realPolynomial p).derivative (realPolynomial (gcdDerivative p)) := by
  have h := common_map (semantics p) (semantics p).derivative (semantics (gcdDerivative p)) (common p) (Rat.castHom ℝ)
  simpa only [realPolynomial,Polynomial.derivative_map] using h

theorem real_decomposition (p : Data) : realPolynomial p=realPolynomial (gcdDerivative p)*realPolynomial (run p) := by
  have h := congrArg (fun f : Polynomial ℚ => f.map (Rat.castHom ℝ)) (decomposition p)
  simpa only [realPolynomial,Polynomial.map_mul] using h

theorem real_roots_preserved (p : Data) (hp : semantics p≠0) (x : ℝ) :
    (realPolynomial (run p)).IsRoot x ↔ (realPolynomial p).IsRoot x :=
  roots_preserved _ _ _ (real_nonzero p hp) (real_common p) (real_decomposition p) x

theorem real_simple_roots (p : Data) (hp : semantics p≠0) (x : ℝ)
    (hx : (realPolynomial (run p)).IsRoot x) : ¬(realPolynomial (run p)).derivative.IsRoot x :=
  quotient_simple_roots _ _ _ (real_nonzero p hp) (real_common p) (real_decomposition p) x hx

theorem real_evaluate (p : Data) (x : ℝ) : (realPolynomial p).eval x=PlayerSpecificSturmVariations.realEvaluate p x := by
  simpa only [realPolynomial,Polynomial.eval_map] using PlayerSpecificSturmVariations.realEvaluate_semantics p x

theorem evaluated_roots_preserved (p : Data) (hp : semantics p≠0) (x : ℝ) :
    PlayerSpecificSturmVariations.realEvaluate (run p) x=0 ↔ PlayerSpecificSturmVariations.realEvaluate p x=0 := by
  have h := real_roots_preserved p hp x
  simpa only [Polynomial.IsRoot,real_evaluate] using h

end Blotto.PlayerSpecificSquarefreeAlgorithm
