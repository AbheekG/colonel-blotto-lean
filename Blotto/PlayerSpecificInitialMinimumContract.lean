import Blotto.PlayerSpecificInitialMinimumCost

/-! Original rational input now reaches actual cached initial arrays and
a positive dyadic minimum, with exact rejection and polynomial source
resources. The bounded coupling/draw is the next separate stage. -/
namespace Blotto.PlayerSpecificInitialMinimumContract
open PlayerSpecificDensePolynomial PlayerSpecificSturmVariations PlayerSpecificAlgebraicReduction
open PlayerSpecificAlgebraicInitialVectorBudget PlayerSpecificInitialMinimumValues
set_option autoImplicit false
set_option maxHeartbeats 2500000
attribute [local irreducible] PlayerSpecificMinimumSearch.search

def InputConstraints {N : ℕ} (m : Data) (budget : ℚ) (p : PlayerSpecificAlgebraicInitialVector.Result N) (x : ℝ) : Prop :=
  Reduced m p.inverseScale ∧
  (∀ j,Reduced m (p.rows.read j).length ∧ Reduced m (p.rows.read j).initialA ∧ Reduced m (p.rows.read j).initialB) ∧
  (∀ j,(0<realEvaluate (p.rows.read j).length x ∧ realEvaluate (p.rows.read j).length x≤(budget:ℝ)) ∧
    (0≤realEvaluate (p.rows.read j).initialA x ∧ realEvaluate (p.rows.read j).initialA x≤realEvaluate (p.rows.read j).length x) ∧
    (0≤realEvaluate (p.rows.read j).initialB x ∧ realEvaluate (p.rows.read j).initialB x≤realEvaluate (p.rows.read j).length x)) ∧
  (∑ j,realEvaluate (p.rows.read j).initialA x)=2 ∧ (∑ j,realEvaluate (p.rows.read j).initialB x)=2*(budget:ℝ)

theorem pure_constraints {N : ℕ} (i : RationalPlayerSpecificInput N) (r : PlayerSpecificFiniteParameterReturn.Result)
    (hr : (PlayerSpecificFiniteParameterDescription.run i).parameters=some r) :
    ∃ x : ℝ,PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x ∧
      InputConstraints r.root.polynomial i.budget (PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r) x :=
  PlayerSpecificAlgebraicInitialContract.actual_coupling_input i r hr

theorem none_iff {N : ℕ} (i : RationalPlayerSpecificInput N) :
    (PlayerSpecificInitialMinimumExecution.run i).1=none ↔ (PlayerSpecificFiniteParameterDescription.run i).parameters=none := by
  unfold PlayerSpecificInitialMinimumExecution.run
  dsimp only
  split
  · simpa only [true_iff] using (by assumption : (PlayerSpecificFiniteParameterDescription.run i).parameters=none)
  · rename_i r h
    simp only [Option.some_ne_none,h]

theorem rejection_iff {N : ℕ} (i : RationalPlayerSpecificInput N) :
    (PlayerSpecificInitialMinimumExecution.run i).1=none ↔ ¬∃ gamma sigma,
      PlayerSpecificRecognition.ValidParameters i.valuesA.values i.valuesB.values (i.budget:ℝ) gamma sigma :=
  (none_iff i).trans (PlayerSpecificFiniteParameterDescriptionContract.rejection_iff i)

theorem selected {N : ℕ} (i : RationalPlayerSpecificInput N) (p : PlayerSpecificInitialMinimumExecution.Prepared N)
    (hp : (PlayerSpecificInitialMinimumExecution.run i).1=some p) :
    ∃ r,(PlayerSpecificFiniteParameterDescription.run i).parameters=some r ∧ p=(PlayerSpecificInitialMinimumExecution.accept i r).1 := by
  unfold PlayerSpecificInitialMinimumExecution.run at hp
  dsimp only at hp
  split at hp
  · cases hp
  · rename_i r hr
    exact ⟨r,hr,(Option.some.inj hp).symm⟩

theorem accepted {N : ℕ} (i : RationalPlayerSpecificInput N) (p : PlayerSpecificInitialMinimumExecution.Prepared N)
    (hp : (PlayerSpecificInitialMinimumExecution.run i).1=some p) :
    ∃ r x,(PlayerSpecificFiniteParameterDescription.run i).parameters=some r ∧
      p.initial.parameters=r ∧
      PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x ∧
      InputConstraints r.root.polynomial i.budget p.initial x ∧
      p.minimum.quantum=PlayerSpecificPositiveFieldLowerBound.dyadic p.minimum.exponent ∧ 0<p.minimum.quantum ∧
      p.minimum.exponent≤PlayerSpecificInitialPositivePrecision.coefficient*(N+1)*(inputSize i+1) ∧
      ∀ j,(p.minimum.quantum:ℝ)≤realEvaluate (p.initial.rows.read j).length x := by
  obtain ⟨r,hr,rfl⟩:=selected i p hp
  obtain ⟨x,hx,hdata⟩:=pure_constraints i r hr
  obtain ⟨y,hy,hq,hpos,he,hl⟩:=actual_minimum i r hr
  have hxy : y=x := hx.2.2 y hy.1 hy.2.1
  subst y
  have hactual : InputConstraints r.root.polynomial i.budget (PlayerSpecificInitialMinimumExecution.accept i r).1.initial x :=
    (initial_value i r).symm ▸ hdata
  have he' : (PlayerSpecificInitialMinimumExecution.accept i r).1.minimum.exponent≤
      PlayerSpecificInitialPositivePrecision.coefficient*(N+1)*(inputSize i+1) :=
    he.trans_eq (PlayerSpecificMinimumContract.fuel_value i)
  exact ⟨r,x,hr,parameters_value i r,hx,hactual,hq,hpos,he',hl⟩

theorem actual_contract {N : ℕ} (i : RationalPlayerSpecificInput N) :
    (PlayerSpecificInitialMinimumExecution.run i).2≤PlayerSpecificInitialMinimumCost.totalBound N (inputSize i) ∧
      ((PlayerSpecificInitialMinimumExecution.run i).1=none ↔ ¬∃ gamma sigma,
        PlayerSpecificRecognition.ValidParameters i.valuesA.values i.valuesB.values (i.budget:ℝ) gamma sigma) ∧
      ∀ p,(PlayerSpecificInitialMinimumExecution.run i).1=some p →
        ∃ r x,(PlayerSpecificFiniteParameterDescription.run i).parameters=some r ∧
          p.initial.parameters=r ∧
          PlayerSpecificSelectedRefinement.Unique r.root.polynomial r.root.interval x ∧
          InputConstraints r.root.polynomial i.budget p.initial x ∧
          p.minimum.quantum=PlayerSpecificPositiveFieldLowerBound.dyadic p.minimum.exponent ∧ 0<p.minimum.quantum ∧
          p.minimum.exponent≤PlayerSpecificInitialPositivePrecision.coefficient*(N+1)*(inputSize i+1) ∧
          ∀ j,(p.minimum.quantum:ℝ)≤realEvaluate (p.initial.rows.read j).length x :=
  ⟨PlayerSpecificInitialMinimumCost.source_cost i,rejection_iff i,accepted i⟩

end Blotto.PlayerSpecificInitialMinimumContract
