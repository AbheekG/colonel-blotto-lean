import Blotto.PlayerSpecificDensePolynomial

/-! Canonical leading-zero removal and exact degree information for the
executable rational representation. These permit bounded Euclidean steps
without using Mathlib's noncomputable polynomial division at runtime. -/
namespace Blotto.PlayerSpecificPolynomialNormalization
open PlayerSpecificDensePolynomial
set_option autoImplicit false
set_option maxHeartbeats 3000000

def Normalized (p : Data) : Prop := p=[] ∨ p.getLast?.getD 0≠0

theorem trim_normalized (p : Data) : Normalized (trim p) := by
  induction p with
  | nil => exact Or.inl rfl
  | cons a p ih =>
    cases ht : trim p with
    | nil =>
      by_cases ha : a=0
      · simp only [trim,ht,ha,and_self,ite_true]
        exact Or.inl rfl
      · simp only [trim,ht,ha,and_false,ite_false]
        exact Or.inr ha
    | cons b tail =>
      simp only [trim,ht,List.cons_ne_nil,false_and,ite_false]
      rw [ht] at ih
      rcases ih with hz | hlast
      · cases hz
      · exact Or.inr (by simpa only [List.getLast?_cons_cons] using hlast)

theorem coefficient (p : Data) (j : ℕ) : (semantics p).coeff j=(p[j]?).getD 0 := by
  induction p generalizing j with
  | nil => simp only [semantics,Polynomial.coeff_zero,List.getElem?_nil,Option.getD_none]
  | cons a p ih =>
    cases j with
    | zero => simp only [semantics,Polynomial.coeff_add,Polynomial.coeff_C_zero,
        Polynomial.coeff_X_mul_zero,add_zero,List.getElem?_cons_zero,Option.getD_some]
    | succ j => simp only [semantics,Polynomial.coeff_add,Polynomial.coeff_C_succ,
        Polynomial.coeff_X_mul,zero_add,ih,List.getElem?_cons_succ]

theorem degree_le (p : Data) : (semantics p).natDegree≤p.length-1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [coefficient]
  have he : p[j]?=none := List.getElem?_eq_none (by omega)
  rw [he]
  rfl

theorem last_coefficient (p : Data) : (semantics p).coeff (p.length-1)=p.getLast?.getD 0 := by
  rw [coefficient,List.getLast?_eq_getElem?]

theorem nonzero (p : Data) (hn : Normalized p) (hp : p≠[]) : semantics p≠0 := by
  have hlast := hn.resolve_left hp
  intro hz
  have hc := congrArg (fun f : Polynomial ℚ => f.coeff (p.length-1)) hz
  rw [last_coefficient,Polynomial.coeff_zero] at hc
  exact hlast hc

theorem degree_eq (p : Data) (hn : Normalized p) (hp : p≠[]) : (semantics p).natDegree=p.length-1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (degree_le p)
  rw [last_coefficient]
  exact hn.resolve_left hp

theorem leading_coefficient (p : Data) (hn : Normalized p) (hp : p≠[]) :
    (semantics p).leadingCoeff=p.getLast?.getD 0 := by
  rw [Polynomial.leadingCoeff,degree_eq p hn hp,last_coefficient]

theorem trim_nil_iff (p : Data) : trim p=[] ↔ semantics p=0 := by
  constructor
  · intro h
    rw [← trim_semantics p,h]
    rfl
  · intro hz
    by_contra hn
    have hne := nonzero (trim p) (trim_normalized p) hn
    exact hne ((trim_semantics p).trans hz)

theorem normalized_length {p : Data} (hn : Normalized p) (N : ℕ)
    (h : (semantics p).natDegree<N) : p.length≤N := by
  by_cases hp : p=[]
  · simp only [hp,List.length_nil]; omega
  · rw [degree_eq p hn hp] at h
    omega

end Blotto.PlayerSpecificPolynomialNormalization
