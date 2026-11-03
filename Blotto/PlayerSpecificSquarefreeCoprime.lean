import Blotto.PlayerSpecificSquarefreeAlgorithm
import Blotto.PlayerSpecificExtendedGCD
import Mathlib.RingTheory.AdjoinRoot

/-! The executed squarefree quotient is coprime to its derivative over Q.
The proof also handles nonreal roots: an irreducible common factor would
give a repeated root in its root field. No root-field data is executed. -/
namespace Blotto.PlayerSpecificSquarefreeCoprime
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization
open PlayerSpecificSquarefreeReduction PlayerSpecificSquarefreeAlgorithm
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem mapped_simple {K : Type*} [Field K] [CharZero K] (f : ℚ →+* K)
    (p : Data) (hp : semantics p≠0) (x : K)
    (hx : ((semantics (PlayerSpecificSquarefreeAlgorithm.run p)).map f).IsRoot x) :
    ¬((semantics (PlayerSpecificSquarefreeAlgorithm.run p)).map f).derivative.IsRoot x := by
  have hn : (semantics p).map f≠0 := fun h => hp ((Polynomial.map_eq_zero f).mp h)
  have hc := common_map (semantics p) (semantics p).derivative (semantics (gcdDerivative p)) (common p) f
  have hd := congrArg (fun q : Polynomial ℚ => q.map f) (decomposition p)
  rw [Polynomial.map_mul] at hd
  rw [← Polynomial.derivative_map] at hc
  exact quotient_simple_roots _ _ _ hn hc hd x hx

def certificate (p : Data) : PlayerSpecificExtendedGCD.Result :=
  let h := PlayerSpecificSquarefreeAlgorithm.run p
  PlayerSpecificExtendedGCD.run h (derivative h)

theorem gcd_unit (p : Data) (hp : semantics p≠0) : IsUnit (semantics (certificate p).gcd) := by
  classical
  let h := PlayerSpecificSquarefreeAlgorithm.run p
  have hh : semantics h≠0 := quotient_nonzero _ _ _ hp (decomposition p)
  have hc : ∀ r : Polynomial ℚ,r∣semantics (certificate p).gcd ↔ r∣semantics h ∧ r∣(semantics h).derivative := by
    intro r
    simpa only [certificate,h,derivative_semantics] using PlayerSpecificExtendedGCD.common_divisors h (derivative h) r
  have hg : semantics (certificate p).gcd≠0 := gcd_nonzero _ _ _ hh hc
  by_contra hn
  obtain ⟨f,hf,hfg⟩ := WfDvdMonoid.exists_irreducible_factor hn hg
  have : Fact (Irreducible f) := ⟨hf⟩
  have : CharZero (AdjoinRoot f) := by
    constructor
    intro m n he
    apply (Nat.cast_injective (R := ℚ))
    apply (AdjoinRoot.of f).injective
    simpa only [map_natCast] using he
  have hd := (hc f).mp hfg
  have hr := AdjoinRoot.isRoot_root f
  have hleft := hr.dvd (Polynomial.map_dvd (AdjoinRoot.of f) hd.1)
  have hright := hr.dvd (Polynomial.map_dvd (AdjoinRoot.of f) hd.2)
  rw [← Polynomial.derivative_map] at hright
  exact mapped_simple (AdjoinRoot.of f) p hp (AdjoinRoot.root f) hleft hright

theorem gcd_constant (p : Data) (hp : semantics p≠0) :
    semantics (certificate p).gcd=Polynomial.C ((semantics (certificate p).gcd).coeff 0) :=
  Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_isUnit (gcd_unit p hp))

def unitLeft (p : Data) : Data :=
  scale ((certificate p).gcd.headD 0)⁻¹ (certificate p).left

def unitRight (p : Data) : Data :=
  scale ((certificate p).gcd.headD 0)⁻¹ (certificate p).right

theorem unit_identity (p : Data) (hp : semantics p≠0) :
    semantics (PlayerSpecificSquarefreeAlgorithm.run p)*semantics (unitLeft p)+
      (semantics (PlayerSpecificSquarefreeAlgorithm.run p)).derivative*semantics (unitRight p)=1 := by
  have hi := PlayerSpecificExtendedGCD.run_identity (PlayerSpecificSquarefreeAlgorithm.run p)
    (derivative (PlayerSpecificSquarefreeAlgorithm.run p))
  change semantics (certificate p).gcd=_ at hi
  rw [derivative_semantics] at hi
  change semantics (certificate p).gcd=semantics (PlayerSpecificSquarefreeAlgorithm.run p)*semantics (certificate p).left+
    (semantics (PlayerSpecificSquarefreeAlgorithm.run p)).derivative*semantics (certificate p).right at hi
  have he : (semantics (certificate p).gcd).coeff 0=(certificate p).gcd.headD 0 := by
    rw [coefficient]
    cases (certificate p).gcd <;> rfl
  have hg := gcd_constant p hp
  rw [he] at hg
  have hn : (certificate p).gcd.headD 0≠0 := by
    intro hz
    have hzero : semantics (certificate p).gcd=0 := by rw [hg,hz,Polynomial.C_0]
    exact (gcd_unit p hp).ne_zero hzero
  rw [unitLeft,unitRight,scale_semantics,scale_semantics]
  calc
    _ = Polynomial.C (((certificate p).gcd.headD 0)⁻¹)*semantics (certificate p).gcd := by rw [hi]; ring
    _ = 1 := by rw [hg,← Polynomial.C_mul,inv_mul_cancel₀ hn,Polynomial.C_1]

end Blotto.PlayerSpecificSquarefreeCoprime
