import Blotto.PlayerSpecificRationalRootContract
import Mathlib.Algebra.Polynomial.SpecificDegree

/-! Actual removal of a recovered rational root. The quotient is computed
by the checked dense division, with exact decomposition, nonzero output,
normalization and strict stored-length/degree descent. -/
namespace Blotto.PlayerSpecificLinearFactor
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization
set_option autoImplicit false
set_option maxHeartbeats 3000000

def linear (q : ℚ) : Data := [-q,1]
def quotient (p : Data) (q : ℚ) : Data := (PlayerSpecificPolynomialDivision.run p (linear q)).1

theorem linear_semantics (q : ℚ) : semantics (linear q)=Polynomial.X-Polynomial.C q := by
  simp only [linear,semantics,map_neg,map_one,mul_zero,add_zero,mul_one]
  ring

theorem linear_irreducible (q : ℚ) : Irreducible (semantics (linear q)) := by
  rw [linear_semantics]
  exact Polynomial.irreducible_of_degree_eq_one (Polynomial.degree_X_sub_C q)

theorem linear_nonzero (q : ℚ) : semantics (linear q)≠0 := (linear_irreducible q).ne_zero

theorem root_dvd (p : Data) (q : ℚ) (hq : evaluate p q=0) : semantics (linear q)∣semantics p := by
  rw [linear_semantics,Polynomial.dvd_iff_isRoot,Polynomial.IsRoot,evaluate_semantics]
  exact hq

theorem remainder_zero (p : Data) (q : ℚ) (hq : evaluate p q=0) :
    semantics (PlayerSpecificPolynomialDivision.run p (linear q)).2=0 := by
  rw [←(PlayerSpecificPolynomialDivision.refines p (linear q)).2]
  exact EuclideanDomain.mod_eq_zero.mpr (root_dvd p q hq)

theorem decomposition (p : Data) (q : ℚ) (hq : evaluate p q=0) :
    semantics p=semantics (linear q)*semantics (quotient p q) := by
  have h:=PlayerSpecificPolynomialDivision.reconstruction p (linear q)
  rw [remainder_zero p q hq,add_zero] at h
  exact h.symm

theorem quotient_nonzero (p : Data) (hp : semantics p≠0) (q : ℚ) (hq : evaluate p q=0) :
    semantics (quotient p q)≠0 := by
  intro hz
  exact hp (by rw [decomposition p q hq,hz,mul_zero])

theorem degree_drop (p : Data) (hp : semantics p≠0) (q : ℚ) (hq : evaluate p q=0) :
    (semantics (quotient p q)).natDegree+1=(semantics p).natDegree := by
  rw [decomposition p q hq,Polynomial.natDegree_mul (linear_nonzero q) (quotient_nonzero p hp q hq),
    linear_semantics,Polynomial.natDegree_X_sub_C]
  omega

theorem length_drop (p : Data) (hp : semantics p≠0) (q : ℚ) (hq : evaluate p q=0) : (quotient p q).length<p.length := by
  have hnorm:=PlayerSpecificPolynomialDivision.quotient_normalized p (linear q)
  have hne : quotient p q≠[] := by intro hz; exact quotient_nonzero p hp q hq (by rw [hz]; rfl)
  have hdegree:=degree_drop p hp q hq
  have hlen:=degree_eq (quotient p q) hnorm hne
  have hcap:=degree_le p
  have hpos:=List.length_pos_iff.mpr hne
  omega

theorem quotient_root_subset (p : Data) (q x : ℚ) (hq : evaluate p q=0) (hx : evaluate (quotient p q) x=0) :
    evaluate p x=0 := by
  rw [←evaluate_semantics,decomposition p q hq,Polynomial.eval_mul,
    evaluate_semantics,evaluate_semantics,hx,mul_zero]

end Blotto.PlayerSpecificLinearFactor
