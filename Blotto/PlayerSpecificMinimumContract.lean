import Blotto.PlayerSpecificMinimumSearch

/-! The actual sampler minimum search needs no supplied minimum or
precision oracle. Its finite guard is computed from the measured original
rational input and the checked uniform polynomial precision coefficient. -/
namespace Blotto.PlayerSpecificMinimumContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicInitialVector PlayerSpecificMinimumSearch PlayerSpecificPositiveFieldLowerBound
set_option autoImplicit false
set_option maxHeartbeats 2500000

def lengths {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) : List Data :=
  List.ofFn (fun j => (p.rows.read j).length)
def fuel {N : ℕ} (i : RationalPlayerSpecificInput N) : ℕ :=
  PlayerSpecificInitialPositivePrecision.coefficient*(N+1)*
    ((PlayerSpecificInputWidthExecution.run RationalCostModel.schoolbook (PlayerSpecificRecognitionInputHeights.row i)).1+1)
def run {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result) : PlayerSpecificMinimumSearch.Result :=
  search RationalCostModel.schoolbook r.root.polynomial r.root.interval
    (lengths (prepare RationalCostModel.schoolbook i r)) (fuel i) 0 1

theorem fuel_value {N : ℕ} (i : RationalPlayerSpecificInput N) :
    fuel i=PlayerSpecificInitialPositivePrecision.coefficient*(N+1)*
      (PlayerSpecificInitialPositivePrecision.inputSize i+1) := by
  simp only [fuel,PlayerSpecificInputWidthExecution.value]
  rfl

theorem lengths_length {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) : (lengths p).length=N :=
  List.length_ofFn

theorem actual_contract {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    ∃ x : ℝ,PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x ∧
      (run i r).quantum=dyadic (run i r).exponent ∧ 0<(run i r).quantum ∧
      (run i r).exponent≤fuel i ∧ (run i r).checks≤fuel i+1 ∧
      ∀ j,((run i r).quantum:ℝ)≤realEvaluate ((prepare RationalCostModel.schoolbook i r).rows.read j).length x := by
  have hs:=PlayerSpecificFiniteParameterDescriptionContract.accepted_sound i r hr
  obtain ⟨x,hx,hl⟩:=PlayerSpecificInitialPositivePrecision.actual_lower_bounds i r hr
  have hv : r.root.interval.lo<r.root.interval.hi := by exact_mod_cast hx.2.1.1.trans_le hx.2.1.2
  have hf : ∀ a∈lengths (prepare RationalCostModel.schoolbook i r),
      ((dyadic (0+fuel i)):ℝ)≤realEvaluate a x := by
    intro a ha
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp ha
    have he:=((hl j).2.trans_eq (fuel_value i).symm)
    have hd : (dyadic (fuel i):ℝ)≤(dyadic (PlayerSpecificPositiveFieldLowerBound.exponent r.root.polynomial
        ((prepare RationalCostModel.schoolbook i r).rows.read j).length r.root.interval):ℝ) := by
      exact_mod_cast dyadic_antitone he
    simpa only [Nat.zero_add] using hd.trans (hl j).1
  have h:=search_sound RationalCostModel.schoolbook r.root.polynomial r.root.interval
    (lengths (prepare RationalCostModel.schoolbook i r)) hs.1 hs.2.1 hv x hx (fuel i) 0 1 (by norm_num [dyadic]) hf
  simp only [Nat.zero_add] at h
  refine ⟨x,hx,h.1,h.2.2.2.2.1,?_,h.2.2.2.1,?_⟩
  · exact h.2.2.1
  · intro j
    exact h.2.2.2.2.2 _ (List.mem_ofFn.mpr ⟨j,rfl⟩)

theorem exponent_bound {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    (run i r).exponent≤PlayerSpecificInitialPositivePrecision.coefficient*(N+1)*
      (PlayerSpecificInitialPositivePrecision.inputSize i+1) := by
  obtain ⟨_,_,_,_,h,_,_⟩:=actual_contract i r hr
  exact h.trans_eq (fuel_value i)

end Blotto.PlayerSpecificMinimumContract
