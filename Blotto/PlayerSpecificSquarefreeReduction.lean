import Blotto.PlayerSpecificSturmVariations

/-! Mathematical root guarantees for the executed derivative-GCD quotient.
The characterization below is instantiated by the actual coefficient GCD;
it does not provide any runtime numerical data or a root-selection oracle. -/
namespace Blotto.PlayerSpecificSquarefreeReduction
set_option autoImplicit false
set_option maxHeartbeats 3500000

variable {𝕂 : Type*} [Field 𝕂]

def CommonDivisors (p q g : Polynomial 𝕂) : Prop :=
  ∀ r,r∣g ↔ r∣p ∧ r∣q

theorem gcd_nonzero (p q g : Polynomial 𝕂) (hp : p≠0) (hg : CommonDivisors p q g) : g≠0 := by
  intro hz
  have hd := ((hg g).mp dvd_rfl).1
  rw [hz,zero_dvd_iff] at hd
  exact hp hd

theorem gcd_multiplicity (p q g : Polynomial 𝕂) (hp : p≠0) (hq : q≠0)
    (hg : CommonDivisors p q g) (x : 𝕂) :
    g.rootMultiplicity x=min (p.rootMultiplicity x) (q.rootMultiplicity x) := by
  have hg0 := gcd_nonzero p q g hp hg
  apply le_antisymm
  · have hd := (hg ((Polynomial.X-Polynomial.C x)^(g.rootMultiplicity x))).mp
      (Polynomial.pow_rootMultiplicity_dvd g x)
    exact le_min ((Polynomial.le_rootMultiplicity_iff hp).mpr hd.1)
      ((Polynomial.le_rootMultiplicity_iff hq).mpr hd.2)
  · apply (Polynomial.le_rootMultiplicity_iff hg0).mpr
    apply (hg _).mpr
    exact ⟨(Polynomial.le_rootMultiplicity_iff hp).mp (min_le_left _ _),
      (Polynomial.le_rootMultiplicity_iff hq).mp (min_le_right _ _)⟩

theorem quotient_nonzero (p g h : Polynomial 𝕂) (hp : p≠0) (hf : p=g*h) : h≠0 := by
  intro hz
  apply hp
  rw [hf,hz,mul_zero]

theorem quotient_root_implies (p g h : Polynomial 𝕂) (hf : p=g*h) (x : 𝕂) (hx : h.IsRoot x) : p.IsRoot x := by
  change p.eval x=0
  rw [hf,Polynomial.eval_mul,hx, mul_zero]

theorem roots_preserved [CharZero 𝕂] (p g h : Polynomial 𝕂) (hp : p≠0)
    (hg : CommonDivisors p p.derivative g) (hf : p=g*h) (x : 𝕂) : h.IsRoot x ↔ p.IsRoot x := by
  constructor
  · exact quotient_root_implies p g h hf x
  · intro hx
    rcases ((hg g).mp dvd_rfl).2 with ⟨r,hr⟩
    have hdvd : p∣p.derivative*h := by
      refine ⟨r,?_⟩
      rw [hr,hf]
      ring
    exact Polynomial.isRoot_of_isRoot_of_dvd_derivative_mul hp hdvd hx

theorem derivative_nonzero_at_root [CharZero 𝕂] (p : Polynomial 𝕂) (hp : p≠0) (x : 𝕂)
    (hx : p.IsRoot x) : p.derivative≠0 := by
  intro hd
  have he := Polynomial.eq_C_of_derivative_eq_zero hd
  rw [he] at hp hx
  exact Polynomial.not_isRoot_C _ _ (Polynomial.C_ne_zero.mp hp) hx

theorem quotient_multiplicity [CharZero 𝕂] (p g h : Polynomial 𝕂) (hp : p≠0)
    (hg : CommonDivisors p p.derivative g) (hf : p=g*h) (x : 𝕂) (hx : p.IsRoot x) :
    h.rootMultiplicity x=1 := by
  have hd0 := derivative_nonzero_at_root p hp x hx
  have hgm := gcd_multiplicity p p.derivative g hp hd0 hg x
  rw [Polynomial.derivative_rootMultiplicity_of_root hx] at hgm
  have hmin : min (p.rootMultiplicity x) (p.rootMultiplicity x-1)=p.rootMultiplicity x-1 :=
    min_eq_right (Nat.sub_le _ _)
  rw [hmin] at hgm
  have hprod : g*h≠0 := by rw [← hf]; exact hp
  have hm := Polynomial.rootMultiplicity_mul (x := x) hprod
  rw [← hf,hgm] at hm
  have hpos := (Polynomial.rootMultiplicity_pos hp).mpr hx
  omega

theorem quotient_simple_roots [CharZero 𝕂] (p g h : Polynomial 𝕂) (hp : p≠0)
    (hg : CommonDivisors p p.derivative g) (hf : p=g*h) (x : 𝕂) (hx : h.IsRoot x) :
    ¬h.derivative.IsRoot x := by
  intro hd
  have hm := quotient_multiplicity p g h hp hg hf x (quotient_root_implies p g h hf x hx)
  have htwo := (Polynomial.one_lt_rootMultiplicity_iff_isRoot (quotient_nonzero p g h hp hf)).mpr ⟨hx,hd⟩
  rw [hm] at htwo
  omega

end Blotto.PlayerSpecificSquarefreeReduction
