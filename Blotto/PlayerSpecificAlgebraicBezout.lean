import Blotto.PlayerSpecificModularHorner

/-! Actual unit Bezout certificates for nonzero reduced field elements.
Irreducibility certifies the computed gcd is a nonzero constant; its actual
head is inverted and both returned coefficient lists are scaled. -/
namespace Blotto.PlayerSpecificAlgebraicBezout
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
set_option autoImplicit false
set_option maxHeartbeats 2000000

def certificate (m a : Data) : PlayerSpecificExtendedGCD.Result := PlayerSpecificExtendedGCD.run m a
def left (m a : Data) : Data := scale ((certificate m a).gcd.headD 0)⁻¹ (certificate m a).left
def right (m a : Data) : Data := scale ((certificate m a).gcd.headD 0)⁻¹ (certificate m a).right

theorem not_dvd (m a : Data) (ha : semantics a≠0) (hdeg : (semantics a).natDegree<(semantics m).natDegree) :
    ¬semantics m∣semantics a := by
  intro hd
  have hh:=Polynomial.natDegree_le_of_dvd hd ha
  omega

theorem gcd_unit (m a : Data) (hm : Irreducible (semantics m)) (ha : semantics a≠0)
    (hdeg : (semantics a).natDegree<(semantics m).natDegree) : IsUnit (semantics (certificate m a).gcd) := by
  have hd:=(PlayerSpecificExtendedGCD.common_divisors m a (semantics (certificate m a).gcd)).mp dvd_rfl
  rcases hm.dvd_iff.mp hd.1 with hu | hassoc
  · exact hu
  · exact (not_dvd m a ha hdeg (hassoc.dvd.trans hd.2)).elim

theorem gcd_constant (m a : Data) (hm : Irreducible (semantics m)) (ha : semantics a≠0)
    (hdeg : (semantics a).natDegree<(semantics m).natDegree) :
    semantics (certificate m a).gcd=Polynomial.C ((certificate m a).gcd.headD 0) := by
  have hc:=Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_isUnit (gcd_unit m a hm ha hdeg))
  have he : (semantics (certificate m a).gcd).coeff 0=(certificate m a).gcd.headD 0 := by
    rw [coefficient]
    cases (certificate m a).gcd <;> rfl
  rwa [he] at hc

theorem unit_identity (m a : Data) (hm : Irreducible (semantics m)) (ha : semantics a≠0)
    (hdeg : (semantics a).natDegree<(semantics m).natDegree) :
    semantics m*semantics (left m a)+semantics a*semantics (right m a)=1 := by
  have hg:=gcd_constant m a hm ha hdeg
  have hn : (certificate m a).gcd.headD 0≠0 := by
    intro hz
    exact (gcd_unit m a hm ha hdeg).ne_zero (by rw [hg,hz,Polynomial.C_0])
  have hi:=PlayerSpecificExtendedGCD.run_identity m a
  change semantics (certificate m a).gcd=semantics m*semantics (certificate m a).left+
    semantics a*semantics (certificate m a).right at hi
  rw [left,right,scale_semantics,scale_semantics]
  calc
    _ = Polynomial.C (((certificate m a).gcd.headD 0)⁻¹)*semantics (certificate m a).gcd := by rw [hi]; ring
    _ = 1 := by rw [hg,←Polynomial.C_mul,inv_mul_cancel₀ hn,Polynomial.C_1]

theorem real_identity (m a : Data) (hm : Irreducible (semantics m)) (ha : semantics a≠0)
    (hdeg : (semantics a).natDegree<(semantics m).natDegree) (x : ℝ) (hx : realEvaluate m x=0) :
    realEvaluate a x*realEvaluate (right m a) x=1 := by
  have hi:=congrArg (fun p : Polynomial ℚ => p.eval₂ (Rat.castHom ℝ) x) (unit_identity m a hm ha hdeg)
  simpa only [Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_one,realEvaluate_semantics,hx,zero_mul,zero_add] using hi

end Blotto.PlayerSpecificAlgebraicBezout
