import Blotto.PlayerSpecificRootContract
import Blotto.RationalLatticeWords

/-! Executable denominator clearing for dense rational polynomials. Its
integer coefficient list scales the original polynomial by one positive
computed denominator; fixed-degree coefficients retain linear bit height. -/
namespace Blotto.PlayerSpecificIntegerPolynomial
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights
set_option autoImplicit false
set_option maxHeartbeats 5000000

def denominator (p : Data) : ℕ := (p.map Rat.den).prod
def clear (p : Data) : List ℤ := p.map (latticeNumerator (denominator p))
def rationalData (p : Data) : Data := (clear p).map (fun (a : ℤ) => (a:ℚ))

theorem denominator_pos (p : Data) : 0<denominator p := by
  induction p with
  | nil => exact Nat.zero_lt_one
  | cons q p ih =>
    change 0<q.den*denominator p
    exact Nat.mul_pos q.den_pos ih

theorem denominator_dvd (p : Data) (q : ℚ) (hq : q∈p) : q.den∣denominator p := by
  induction p with
  | nil => cases hq
  | cons a p ih =>
    change q.den∣a.den*denominator p
    rcases List.mem_cons.mp hq with he | ht
    · subst q; exact dvd_mul_right _ _
    · exact dvd_mul_of_dvd_right (ih ht) _

theorem rationalData_value (p : Data) : rationalData p=scale (denominator p:ℚ) p := by
  unfold rationalData clear scale
  rw [List.map_map]
  apply List.map_congr_left
  intro q hq
  simpa only [Function.comp_apply,mul_comm] using latticeNumerator_cast_eq_mul (denominator_dvd p q hq)

theorem semantics_value (p : Data) :
    semantics (rationalData p)=Polynomial.C (denominator p:ℚ)*semantics p := by
  rw [rationalData_value,scale_semantics]

theorem roots (p : Data) (x : ℚ) : evaluate (rationalData p) x=0 ↔ evaluate p x=0 := by
  have hD : (denominator p:ℚ)≠0 := by exact_mod_cast (denominator_pos p).ne'
  rw [←evaluate_semantics,semantics_value,Polynomial.eval_mul,Polynomial.eval_C,evaluate_semantics,mul_eq_zero]
  exact or_iff_right hD

theorem length (p : Data) : (clear p).length=p.length := List.length_map _

theorem cast_last (p : List ℤ) :
    ((p.map (fun (a : ℤ) => (a:ℚ))).getLast?.getD 0)=((p.getLast?.getD 0:ℤ):ℚ) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    cases p with
    | nil => rfl
    | cons b p => simpa only [List.map_cons,List.getLast?_cons_cons] using ih

theorem scale_last (p : Data) (a : ℚ) :
    (scale a p).getLast?.getD 0=a*(p.getLast?.getD 0) := by
  induction p with
  | nil => simp only [scale,List.map_nil,List.getLast?_nil,Option.getD_none,mul_zero]
  | cons b p ih =>
    cases p with
    | nil => rfl
    | cons c p => simpa only [scale,List.map_cons,List.getLast?_cons_cons] using ih

theorem clear_last (p : Data) :
    (((clear p).getLast?.getD 0:ℤ):ℚ)=(denominator p:ℚ)*(p.getLast?.getD 0) := by
  rw [←cast_last]
  change (rationalData p).getLast?.getD 0=_
  rw [rationalData_value,scale_last]

theorem leading_nonzero (p : Data) (hp : PlayerSpecificPolynomialNormalization.Normalized p) (hne : p≠[]) :
    (clear p).getLast?.getD 0≠0 := by
  have hlast:=hp.resolve_left hne
  have hD : (denominator p:ℚ)≠0 := by exact_mod_cast (denominator_pos p).ne'
  intro hz
  have h:=clear_last p
  rw [hz,Int.cast_zero] at h
  exact (mul_ne_zero hD hlast) h.symm

theorem denominator_bound (p : Data) (H : ℕ) (hp : HasHeight p H) : denominator p≤2^(p.length*H) := by
  induction p with
  | nil => simp only [denominator,List.map_nil,List.prod_nil,List.length_nil,Nat.zero_mul,pow_zero,Nat.le_refl]
  | cons q p ih =>
    have hq := (head_height hp).2.le
    have ht := ih (tail_height hp)
    change q.den*denominator p≤2^((p.length+1)*H)
    rw [Nat.add_mul,Nat.one_mul,pow_add]
    exact (Nat.mul_le_mul hq ht).trans_eq (Nat.mul_comm _ _)

theorem coefficient_bound (p : Data) (H : ℕ) (hp : HasHeight p H) (hlen : p.length≤4) :
    ∀ a∈clear p,a.natAbs<2^(5*H) := by
  intro a ha
  obtain ⟨q,hq,rfl⟩:=List.mem_map.mp ha
  have hD:denominator p≤2^(4*H) := (denominator_bound p H hp).trans
    (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right H hlen))
  have hn:=(hp q hq).1
  have hquot:=Nat.div_le_self (denominator p) q.den
  rw [latticeNumerator,Int.natAbs_mul,Int.natAbs_natCast]
  calc
    q.num.natAbs*(denominator p/q.den)≤q.num.natAbs*2^(4*H) := Nat.mul_le_mul_left _ (hquot.trans hD)
    _ < 2^H*2^(4*H) := Nat.mul_lt_mul_of_pos_right hn (Nat.two_pow_pos _)
    _ = 2^(5*H) := by rw [←pow_add]; congr 1; omega

end Blotto.PlayerSpecificIntegerPolynomial
