import Blotto.PlayerSpecificSturmSequence

/-! Sign-variation identities needed for Sturm root counting. A zero of
an internal row does not affect the count when its neighbours have opposite
signs. Executable rational endpoint counts agree with real evaluation. -/
namespace Blotto.PlayerSpecificSturmVariations
open SignType PlayerSpecificDensePolynomial
set_option autoImplicit false
set_option maxHeartbeats 3000000

theorem sign_choice {α : Type*} [Zero α] [LinearOrder α] (a b c : α)
    (ha : a≠0) (hb : b≠0) (hc : c≠0) (hac : sign a≠sign c) :
    sign b=sign a ∨ sign b=sign c := by
  rcases sign_eq_sign_or_eq_neg hb ha with hba | hba
  · exact Or.inl hba
  · rcases sign_eq_sign_or_eq_neg hc ha with hca | hca
    · exact False.elim (hac hca.symm)
    · exact Or.inr (hba.trans hca.symm)

theorem opposite_middle {α : Type*} [Zero α] [LinearOrder α] (a b c : α) (rest : List α)
    (ha : a≠0) (hc : c≠0) (hac : sign a≠sign c) :
    (a::b::c::rest).signVariations=(c::rest).signVariations+1 := by
  by_cases hb : b=0
  · subst b
    rw [List.signVariations_cons_zero_cons,List.signVariations_cons_cons_of_ne_zero rest ha hc]
    simp only [hac,ite_false]
  · rw [List.signVariations_cons_cons_of_ne_zero (c::rest) ha hb,
      List.signVariations_cons_cons_of_ne_zero rest hb hc]
    rcases sign_choice a b c ha hb hc hac with hba | hbc
    · simp only [hba,hac,ite_false,ite_true,add_zero]
    · simp only [hbc,hac,ite_false,ite_true,add_zero]

theorem opposite_middle_replace {α : Type*} [Zero α] [LinearOrder α] (a b b' c : α) (rest : List α)
    (ha : a≠0) (hc : c≠0) (hac : sign a≠sign c) :
    (a::b::c::rest).signVariations=(a::b'::c::rest).signVariations := by
  rw [opposite_middle a b c rest ha hc hac,opposite_middle a b' c rest ha hc hac]

theorem rational_sign_cast (q : ℚ) : sign (q : ℝ)=sign q := by
  simp only [sign_apply,Rat.cast_pos,Rat.cast_lt_zero]

theorem variations_cast (xs : List ℚ) :
    (xs.map (fun (q : ℚ) => (q : ℝ))).signVariations=xs.signVariations :=
  List.signVariations_map rational_sign_cast xs

noncomputable def realEvaluate (p : Data) (x : ℝ) : ℝ :=
  p.foldr (fun (a : ℚ) (rest : ℝ) => (a : ℝ)+x*rest) 0

theorem realEvaluate_semantics (p : Data) (x : ℝ) :
    (semantics p).eval₂ (Rat.castHom ℝ) x=realEvaluate p x := by
  induction p with
  | nil => simp only [semantics,Polynomial.eval₂_zero,realEvaluate,List.foldr_nil]
  | cons a p ih =>
    simp only [semantics,Polynomial.eval₂_add,Polynomial.eval₂_C,Polynomial.eval₂_mul,
      Polynomial.eval₂_X,ih,realEvaluate,List.foldr_cons]
    rfl

theorem evaluate_cast (p : Data) (x : ℚ) : realEvaluate p (x : ℝ)=(evaluate p x : ℝ) := by
  induction p with
  | nil => simp only [realEvaluate,evaluate,List.foldr_nil,Rat.cast_zero]
  | cons a p ih => simp only [realEvaluate,evaluate,List.foldr_cons,Rat.cast_add,Rat.cast_mul]
                   exact congrArg (fun z => (a : ℝ)+(x : ℝ)*z) ih

theorem endpoint_variations (rows : List Data) (x : ℚ) :
    (rows.map (fun p => realEvaluate p (x : ℝ))).signVariations=PlayerSpecificSturmSequence.variations rows x := by
  have h := variations_cast (rows.map (fun p => evaluate p x))
  simpa only [List.map_map,Function.comp_def,← evaluate_cast,PlayerSpecificSturmSequence.variations] using h

end Blotto.PlayerSpecificSturmVariations
