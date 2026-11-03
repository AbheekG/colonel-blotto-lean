import Blotto.PlayerSpecificRationalBreakpoint

/-! Computable finite-bit cell search: test the actual interior algebraic
candidates and then the separate exact rational breakpoint. Soundness is
expressed at the retained unique real root of the returned representation. -/
namespace Blotto.PlayerSpecificFiniteCellSearch
open PlayerSpecificDensePolynomial PlayerSpecificRationalCells PlayerSpecificAlgebraicCandidates PlayerSpecificSturmVariations
set_option autoImplicit false
set_option maxHeartbeats 3000000

def roots (model : RationalCostModel) (c : Cell) (b : ℚ) : List Candidate :=
  (PlayerSpecificCandidateExecution.run model (cubic c.state.coefficients b)).1
def interior (model : RationalCostModel) (c : Cell) (b : ℚ) : Option Candidate :=
  (roots model c b).find? (PlayerSpecificAlgebraicCandidateTest.run model c)
def run (model : RationalCostModel) (c : Cell) (b : ℚ) : Option Candidate :=
  match interior model c b with
  | some r => some r
  | none => PlayerSpecificRationalBreakpoint.run c b

def Good (c : Cell) (b : ℚ) (r : Candidate) : Prop :=
  PlayerSpecificPolynomialNormalization.Normalized r.polynomial ∧ Irreducible (semantics r.polynomial) ∧ r.polynomial.length≤4 ∧
    (∃! x : ℝ,realEvaluate r.polynomial x=0 ∧ r.interval.Contains x) ∧
    ∃! x : ℝ,realEvaluate r.polynomial x=0 ∧ r.interval.Contains x ∧
      x∈PlayerSpecificCellCandidates.candidates (castCell c) (b:ℝ) ∧ PlayerSpecificCellCandidates.Passes (castCell c) (b:ℝ) x

theorem polynomial_nonzero (c : Cell) (b : ℚ) (hp : semantics (cubic c.state.coefficients b)≠0) :
    PlayerSpecificPolynomial.polynomial (castCell c).state.coefficients (b:ℝ)≠0 := by
  rw [←PlayerSpecificRationalIntervals.cubic_cast]
  exact PlayerSpecificSquarefreeAlgorithm.real_nonzero _ hp

theorem interior_sound (model : RationalCostModel) (c : Cell) (b : ℚ) (hb : b≠0)
    (hp : semantics (cubic c.state.coefficients b)≠0) (r : Candidate) (hr : interior model c b=some r) : Good c b r := by
  have hm:=List.mem_of_find?_eq_some hr
  have ht:=List.find?_some hr
  have hf:=PlayerSpecificCandidateFieldInput.field_input model _ hp (by rfl) r hm
  have he:=PlayerSpecificCandidateContract.each model _ hp (by rfl) r hm
  obtain ⟨x,hx,hunique⟩:=hf.2.2.2.2
  have htest:=(PlayerSpecificAlgebraicCandidateTest.correct model _ hp (by rfl) r hm c b hb x hx).mp ht
  have horiginal: realEvaluate (cubic c.state.coefficients b) x=0 := (he.2.2.2 x hx.2).mp hx.1
  have hroot : PlayerSpecificCubic.cubic (castCell c).state.coefficients (b:ℝ) x=0 := by
    rw [←PlayerSpecificRationalIntervals.cubic_value]
    exact horiginal
  have hmem:=PlayerSpecificCellCandidates.complete (castCell c) (b:ℝ) x (polynomial_nonzero c b hp)
    (PlayerSpecificCellCandidates.interior_range (castCell c) x htest.1) htest.1.2.1 hroot
  exact ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.2,⟨x,⟨hx.1,hx.2,hmem,htest.2⟩,
    fun y hy => hunique y ⟨hy.1,hy.2.1⟩⟩⟩

theorem breakpoint_sound (c : Cell) (b : ℚ) (r : Candidate) (hr : PlayerSpecificRationalBreakpoint.run c b=some r) : Good c b r := by
  have hs:=hr
  cases hu : c.upper with
  | none => simp only [PlayerSpecificRationalBreakpoint.run,hu] at hr; cases hr
  | some q =>
    by_cases ht : 0<q ∧ c.lower≤q ∧ evaluate (cubic c.state.coefficients b) q=0 ∧ PlayerSpecificRationalBreakpoint.passes c b q
    · simp only [PlayerSpecificRationalBreakpoint.run,hu,ht] at hr
      have he:=Option.some.inj hr
      subst r
      have hcorrect:=(PlayerSpecificRationalBreakpoint.correct c b q).mp hs
      obtain ⟨x,hx,hunique⟩:=PlayerSpecificRationalBreakpoint.candidate_root q
      have hxeq : x=(q:ℝ) := by
        have hlinear : realEvaluate (PlayerSpecificLinearFactor.linear q) x=0 := hx.1
        exact sub_eq_zero.mp ((PlayerSpecificAlgebraicCandidates.linear_real q x).symm.trans hlinear)
      subst x
      refine ⟨?_,PlayerSpecificLinearFactor.linear_irreducible q,?_,PlayerSpecificRationalBreakpoint.candidate_root q,⟨(q:ℝ),⟨hx.1,hx.2,?_,?_⟩,?_⟩⟩
      · exact Or.inr (by simp only [PlayerSpecificRationalBreakpoint.candidate,PlayerSpecificLinearFactor.linear,
          List.getLast?_cons_cons,List.getLast?_singleton,Option.getD_some]; norm_num)
      · change (PlayerSpecificLinearFactor.linear q).length≤4
        simp only [PlayerSpecificLinearFactor.linear,List.length_cons,List.length_nil]; decide
      · exact List.mem_append_right _ hcorrect.1
      · exact (PlayerSpecificRationalBreakpoint.passes_cast c b q).mp hcorrect.2
      · intro y hy
        exact hunique y ⟨hy.1,hy.2.1⟩
    · simp only [PlayerSpecificRationalBreakpoint.run,hu,ht,ite_false] at hr
      cases hr

theorem sound (model : RationalCostModel) (c : Cell) (b : ℚ) (hb : b≠0)
    (hp : semantics (cubic c.state.coefficients b)≠0) (r : Candidate) (hr : run model c b=some r) : Good c b r := by
  rw [run] at hr
  split at hr
  · rename_i chosen hchosen
    have he:=Option.some.inj hr
    subst chosen
    exact interior_sound model c b hb hp r hchosen
  · exact breakpoint_sound c b r hr

end Blotto.PlayerSpecificFiniteCellSearch
