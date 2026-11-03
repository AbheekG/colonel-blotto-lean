import Blotto.PlayerSpecificCandidateContract

/-! Executable reduced-basis arithmetic at a selected real algebraic root.
Reduction uses actual dense division, and its real-value refinement retains
the selected root rather than making an arbitrary conjugate choice. -/
namespace Blotto.PlayerSpecificAlgebraicReduction
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
set_option autoImplicit false
set_option maxHeartbeats 2000000

def Reduced (m a : Data) : Prop := Normalized a ∧ a.length<m.length
def reduce (m a : Data) : Data := (PlayerSpecificPolynomialDivision.run a m).2

theorem reduced (m a : Data) (hm : Normalized m) (hm0 : m≠[]) : Reduced m (reduce m a) :=
  ⟨PlayerSpecificPolynomialDivision.remainder_normalized a m,PlayerSpecificPolynomialDivision.remainder_length a m hm hm0⟩

theorem nil_reduced (m : Data) (hm : m≠[]) : Reduced m [] :=
  ⟨Or.inl rfl,List.length_pos_iff.mpr hm⟩

theorem real_add (a b : Data) (x : ℝ) : realEvaluate (add a b) x=realEvaluate a x+realEvaluate b x := by
  rw [←realEvaluate_semantics,add_semantics,Polynomial.eval₂_add,realEvaluate_semantics,realEvaluate_semantics]

theorem real_scale (c : ℚ) (a : Data) (x : ℝ) : realEvaluate (scale c a) x=(c:ℝ)*realEvaluate a x := by
  rw [←realEvaluate_semantics,scale_semantics,Polynomial.eval₂_mul,Polynomial.eval₂_C,realEvaluate_semantics]
  rfl

theorem real_shift (a : Data) (x : ℝ) : realEvaluate (shift a) x=x*realEvaluate a x := by
  rw [←realEvaluate_semantics,shift_semantics,Polynomial.eval₂_mul,Polynomial.eval₂_X,realEvaluate_semantics]

theorem real_subtract (a b : Data) (x : ℝ) : realEvaluate (subtract a b) x=realEvaluate a x-realEvaluate b x := by
  rw [←realEvaluate_semantics,subtract_semantics,Polynomial.eval₂_sub,realEvaluate_semantics,realEvaluate_semantics]

theorem real_reduce (m a : Data) (x : ℝ) (hx : realEvaluate m x=0) : realEvaluate (reduce m a) x=realEvaluate a x := by
  have h:=congrArg (fun p : Polynomial ℚ => p.eval₂ (Rat.castHom ℝ) x)
    (PlayerSpecificPolynomialDivision.reconstruction a m)
  rw [Polynomial.eval₂_add,Polynomial.eval₂_mul,realEvaluate_semantics,hx,zero_mul,zero_add,
    realEvaluate_semantics,realEvaluate_semantics] at h
  exact h

theorem degree_lt (m a : Data) (hm : Normalized m) (hm0 : m≠[]) (ha : Reduced m a) (ha0 : semantics a≠0) :
    (semantics a).natDegree<(semantics m).natDegree := by
  have ha' : a≠[] := by intro h; exact ha0 (by rw [h]; rfl)
  have hma:=degree_eq m hm hm0
  have haa:=degree_eq a ha.1 ha'
  have hpos:=List.length_pos_iff.mpr ha'
  have hl:=ha.2
  omega

end Blotto.PlayerSpecificAlgebraicReduction
