import Blotto.PlayerSpecificFiniteSampler

/-! The actual prepared rational sampler inherits every-output hard
budgets and finite output lengths from the original accepted input.
No probability or full source-cost completion is claimed here. -/
namespace Blotto.PlayerSpecificFiniteSamplerContract
open PlayerSpecificFiniteSampler
set_option autoImplicit false
set_option maxHeartbeats 2500000
attribute [local irreducible] PlayerSpecificMinimumSearch.search

theorem base_constraints {N : ℕ} (i : RationalPlayerSpecificInput N) (base : PlayerSpecificInitialMinimumExecution.Prepared N)
    (hb : (PlayerSpecificInitialMinimumExecution.run i).1=some base) :
    ∃ x : ℝ,PlayerSpecificSelectedRefinement.Unique base.initial.parameters.root.polynomial base.initial.parameters.root.interval x ∧
      ∀ (player : Bool) (H K P : ℕ) (bits : Fin (PlayerSpecificAlgebraicFiniteDraw.bitCount N H K) → Bool),
        Blotto.Feasible (if player then 1 else (i.budget:ℝ))
            (PlayerSpecificRationalOutput.allocation (PlayerSpecificRationalFiniteDraw.draw base.initial i.budget player H K P bits)) ∧
          ∀ j,RationalHeight ((PlayerSpecificRationalFiniteDraw.draw base.initial i.budget player H K P bits).read j) (P+2) := by
  obtain ⟨r,hr,hbase⟩ := PlayerSpecificInitialMinimumContract.selected i base hb
  have hi : base.initial=PlayerSpecificAlgebraicInitialVector.prepare RationalCostModel.schoolbook i r := by
    rw [hbase]
    exact PlayerSpecificInitialMinimumValues.initial_value i r
  obtain ⟨x,hx,hdraw⟩ := PlayerSpecificRationalFiniteDraw.original_input i r hr
  refine ⟨x,?_,?_⟩
  · rw [hi]
    exact hx
  · intro player H K P bits
    rw [hi]
    have h := hdraw player H K P bits
    exact ⟨h.1,fun j => (h.2 j).2.2⟩

theorem accepted_draws {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ) (p : Prepared N)
    (hp : prepare i epsilon=some p) :
    p.budget=i.budget ∧
      ∃ x : ℝ,PlayerSpecificSelectedRefinement.Unique p.base.initial.parameters.root.polynomial p.base.initial.parameters.root.interval x ∧
        ∀ (player : Bool) (bits : Fin (bitCount p) → Bool),
          Blotto.Feasible (if player then 1 else (i.budget:ℝ)) (PlayerSpecificRationalOutput.allocation (draw p player bits)) ∧
            ∀ j,RationalHeight ((draw p player bits).read j) (p.accuracy.outputBits+2) := by
  obtain ⟨base,hb,rfl⟩ := selected i epsilon p hp
  obtain ⟨x,hx,hdraw⟩ := base_constraints i base hb
  refine ⟨rfl,x,hx,?_⟩
  intro player bits
  exact hdraw player _ _ _ bits

theorem numerical_metadata {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ) (he : 0 < epsilon)
    (p : Prepared N) (hp : prepare i epsilon=some p) :
    let k := ⌈Real.logb 2 (1/(epsilon:ℝ))⌉₊
    let S := PlayerSpecificInitialPositivePrecision.coefficient*(N+1)*(PlayerSpecificInitialPositivePrecision.inputSize i+1)
    p.base.minimum.quantum=PlayerSpecificPositiveFieldLowerBound.dyadic p.base.minimum.exponent ∧
      0 < p.base.minimum.quantum ∧ p.base.minimum.exponent ≤ S ∧
      p.accuracy.outputBits ≤ S+k+6 ∧
      bitCount p ≤ (N+1000)*(k+binaryWordWidth (N+1000)+6)+2*(k+6) := by
  obtain ⟨base,hb,rfl⟩ := selected i epsilon p hp
  obtain ⟨r,x,hr,hparameters,hroot,hconstraints,hq,hpos,hs,hL⟩ := PlayerSpecificInitialMinimumContract.accepted i base hb
  change base.minimum.exponent ≤ PlayerSpecificInitialPositivePrecision.coefficient*(N+1)*(PlayerSpecificInitialPositivePrecision.inputSize i+1) at hs
  have hacc := PlayerSpecificFiniteAccuracy.logarithmic_bounds N base.minimum.exponent epsilon he
  exact ⟨hq,hpos,hs,by dsimp only [ofBase]; omega,
    PlayerSpecificFiniteAccuracy.random_bit_budget N base.minimum.exponent epsilon he⟩

theorem minimum_lower_bound {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ) (p : Prepared N)
    (hp : prepare i epsilon=some p) :
    ∃ x : ℝ,PlayerSpecificSelectedRefinement.Unique p.base.initial.parameters.root.polynomial p.base.initial.parameters.root.interval x ∧
      ∀ j,(p.base.minimum.quantum:ℝ) ≤ PlayerSpecificSturmVariations.realEvaluate (p.base.initial.rows.read j).length x := by
  obtain ⟨base,hb,rfl⟩ := selected i epsilon p hp
  obtain ⟨r,x,hr,hparameters,hroot,hconstraints,hq,hpos,hs,hL⟩ := PlayerSpecificInitialMinimumContract.accepted i base hb
  refine ⟨x,?_,hL⟩
  change PlayerSpecificSelectedRefinement.Unique base.initial.parameters.root.polynomial base.initial.parameters.root.interval x
  rw [hparameters]
  exact hroot

theorem output_polynomial_sizes {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ) (he : 0 < epsilon)
    (p : Prepared N) (hp : prepare i epsilon=some p) (player : Bool) (bits : Fin (bitCount p) → Bool) :
    ∀ j,RationalHeight ((draw p player bits).read j)
      (PlayerSpecificInitialPositivePrecision.coefficient*(N+1)*(PlayerSpecificInitialPositivePrecision.inputSize i+1)+
        ⌈Real.logb 2 (1/(epsilon:ℝ))⌉₊+8) := by
  obtain ⟨hbudget,x,hx,hdraw⟩ := accepted_draws i epsilon p hp
  have hm := (numerical_metadata i epsilon he p hp).2.2.2.1
  intro j
  exact ((hdraw player bits).2 j).mono (by omega)

theorem numerical_error_budget {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ) (he : 0 < epsilon)
    (p : Prepared N) (hp : prepare i epsilon=some p) :
    3/(2*(2:ℝ)^p.accuracy.scalarBits)+(N+1000:ℝ)/(2:ℝ)^p.accuracy.coinBits+
      (1/(2:ℝ)^p.accuracy.outputBits)/(p.base.minimum.quantum:ℝ) ≤ 3*(epsilon:ℝ)/32 := by
  have hq := (numerical_metadata i epsilon he p hp).1
  have hcast : (p.base.minimum.quantum:ℝ)=1/(2:ℝ)^p.base.minimum.exponent := by
    rw [hq]
    simp only [PlayerSpecificPositiveFieldLowerBound.dyadic,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]
  rw [hcast]
  obtain ⟨base,hb,rfl⟩ := selected i epsilon p hp
  exact PlayerSpecificFiniteAccuracyError.total_error N base.minimum.exponent epsilon he

end Blotto.PlayerSpecificFiniteSamplerContract
