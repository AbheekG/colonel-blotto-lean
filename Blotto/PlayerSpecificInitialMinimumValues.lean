import Blotto.PlayerSpecificInitialMinimumExecution

/-! Proof-only stage views identify the minimum selected from actual
stored initial lengths with the checked halving search. Runtime calls
retain these stages once and never call the views. -/
namespace Blotto.PlayerSpecificInitialMinimumValues
open PlayerSpecificDensePolynomial PlayerSpecificSturmVariations
set_option autoImplicit false
set_option maxHeartbeats 2500000
attribute [local irreducible] PlayerSpecificMinimumSearch.search

def minimum {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result) :=
  PlayerSpecificMinimumSearch.search RationalCostModel.schoolbook r.root.polynomial r.root.interval
    (PlayerSpecificInitialLengthList.run RationalCostModel.schoolbook (PlayerSpecificInitialLengthListCost.stored i r)).1
    (PlayerSpecificMinimumGuardExecution.run RationalCostModel.schoolbook i).1 0 1


theorem minimum_value {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result) :
    minimum i r=PlayerSpecificMinimumContract.run i r := by
  simp only [minimum,PlayerSpecificInitialLengthList.value,PlayerSpecificMinimumGuardExecution.value,
    PlayerSpecificInitialLengthListCost.stored,PlayerSpecificAlgebraicInitialVectorExecution.value,PlayerSpecificMinimumContract.run]


theorem initial_value {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result) :
    (PlayerSpecificInitialMinimumExecution.accept i r).1.initial=PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r :=
  PlayerSpecificAlgebraicInitialVectorExecution.value _ _ _

theorem parameters_value {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result) :
    (PlayerSpecificInitialMinimumExecution.accept i r).1.initial.parameters=r :=
  congrArg (fun p : PlayerSpecificAlgebraicInitialVector.Result N => p.parameters) (initial_value i r)


theorem returned_minimum {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result) :
    (PlayerSpecificInitialMinimumExecution.accept i r).1.minimum=PlayerSpecificMinimumContract.run i r :=
  minimum_value i r

theorem quantum_value {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result) :
    (PlayerSpecificInitialMinimumExecution.accept i r).1.minimum.quantum=(PlayerSpecificMinimumContract.run i r).quantum :=
  congrArg PlayerSpecificMinimumSearch.Result.quantum (returned_minimum i r)

theorem exponent_value {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result) :
    (PlayerSpecificInitialMinimumExecution.accept i r).1.minimum.exponent=(PlayerSpecificMinimumContract.run i r).exponent :=
  congrArg PlayerSpecificMinimumSearch.Result.exponent (returned_minimum i r)

theorem actual_minimum {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    let p:=(PlayerSpecificInitialMinimumExecution.accept i r).1
    ∃ x : ℝ,PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x ∧
      p.minimum.quantum=PlayerSpecificPositiveFieldLowerBound.dyadic p.minimum.exponent ∧ 0<p.minimum.quantum ∧
      p.minimum.exponent≤PlayerSpecificMinimumContract.fuel i ∧ ∀ j,(p.minimum.quantum:ℝ)≤realEvaluate (p.initial.rows.read j).length x := by
  obtain ⟨x,hx,hq,hpos,he,_,hl⟩:=PlayerSpecificMinimumContract.actual_contract i r hr
  have hqv:=quantum_value i r
  have hev:=exponent_value i r
  have hiv:=initial_value i r
  have hlengths : ∀ j,((PlayerSpecificInitialMinimumExecution.accept i r).1.minimum.quantum:ℝ)≤
      realEvaluate ((PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r).rows.read j).length x :=
    hqv.symm ▸ hl
  exact ⟨x,hx,hqv.trans (hq.trans (congrArg PlayerSpecificPositiveFieldLowerBound.dyadic hev).symm),
    hqv.symm ▸ hpos,hev.symm ▸ he,hiv.symm ▸ hlengths⟩

end Blotto.PlayerSpecificInitialMinimumValues
