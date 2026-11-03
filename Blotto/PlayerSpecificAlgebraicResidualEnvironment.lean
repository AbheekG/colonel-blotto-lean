import Blotto.PlayerSpecificAlgebraicNestedFamilyReference
import Blotto.RealNestedResidualCompiler

/-! Actual retained-field residual parameters from the six raw nested
rows. No geometric or residual input is supplied as a runtime oracle. -/
namespace Blotto.PlayerSpecificAlgebraicResidualEnvironment
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicNestedInput
open PlayerSpecificAlgebraicNestedParameterSizes
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def environment (root : Candidate) (a : Input) : FixedArrayTable 5 Data :=
  let u:=PlayerSpecificAlgebraicField.minus root.polynomial a.budget a.first
  let v:=PlayerSpecificAlgebraicField.minus root.polynomial a.budget a.second
  let w:=PlayerSpecificAlgebraicField.minus root.polynomial a.budget a.long
  let h:=PlayerSpecificAlgebraicField.times root.polynomial a.probability
    (PlayerSpecificAlgebraicField.minus root.polynomial a.long a.short)
  FixedArrayTable.ofFn ![u,v,w,h,a.short]

theorem value (root : Candidate) (a : Input) (i : NestedInput) (x : ℝ)
    (hx : realEvaluate root.polynomial x=0) (ha : PlayerSpecificAlgebraicNestedInput.Values a i x)
    (hvt : i.v< i.t) (htu : i.t< i.u) :
    PlayerSpecificAlgebraicExpression.realEnv (environment root a) x=
      RealNestedResidualCode.environment (i.residualInput hvt htu) := by
  unfold PlayerSpecificAlgebraicExpression.realEnv RealNestedResidualCode.environment
  congr 1
  funext j
  fin_cases j <;> simp [environment,FixedArrayTable.read_ofFn,
    PlayerSpecificAlgebraicField.minus_value _ _ _ x hx,PlayerSpecificAlgebraicField.times_value _ _ _ x hx,
    ha.budget,ha.first,ha.second,ha.long,ha.short,ha.probability,
    NestedInput.residualInput,NestedInput.geometry,NestedInput.u,NestedInput.v,NestedInput.h]

theorem bounds (root : Candidate) (a : Input) (T : ℕ) (hfit : Fits root a T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) :
    ∀ j,Reduced root.polynomial ((environment root a).read j) ∧ HasHeight ((environment root a).read j) (iterate 2 T) := by
  have hbase : T≤step T := (Nat.le_succ _).trans (large T)
  have hT2 : T≤ iterate 2 T := PlayerSpecificAlgebraicExpressionBudget.initial_le 2 T
  have hstep2 : step T≤ iterate 2 T := PlayerSpecificAlgebraicExpressionBudget.fuel_mono T (show 1≤2 by omega)
  have hshort : T+T+1≤step T := by
    have h:=calibrate 3 T (by unfold PlayerSpecificAlgebraicHeightEnvelope.coefficient; omega)
    omega
  have hminus : ∀ row,Reduced root.polynomial row → HasHeight row T →
      Reduced root.polynomial (PlayerSpecificAlgebraicField.minus root.polynomial a.budget row) ∧
      HasHeight (PlayerSpecificAlgebraicField.minus root.polynomial a.budget row) (iterate 2 T) := by
    intro row hr hh
    exact ⟨PlayerSpecificAlgebraicField.minus_reduced _ _ _ hm hm0,
      mono (PlayerSpecificShortReduction.minus_height _ _ _ hm hm0 hfit.budget.1 hr T T hfit.budget.2 hh) (hshort.trans hstep2)⟩
  have hdif:=PlayerSpecificShortReduction.minus_height root.polynomial a.long a.short hm hm0 hfit.long.1 hfit.short.1
    T T hfit.long.2 hfit.short.2
  have hprod:=times_height root.polynomial a.probability (PlayerSpecificAlgebraicField.minus root.polynomial a.long a.short)
    (step T) hm hm0 hml hfit.probability.1 (PlayerSpecificAlgebraicField.minus_reduced _ _ _ hm hm0)
    (mono hmT hbase) (mono hfit.probability.2 hbase) (mono hdif hshort)
  intro j
  fin_cases j <;> simp only [environment,FixedArrayTable.read_ofFn]
  · exact hminus a.first hfit.first.1 hfit.first.2
  · exact hminus a.second hfit.second.1 hfit.second.2
  · exact hminus a.long hfit.long.1 hfit.long.2
  · exact ⟨PlayerSpecificAlgebraicField.times_reduced _ _ _ hm hm0,hprod⟩
  · exact ⟨hfit.short.1,mono hfit.short.2 hT2⟩

end Blotto.PlayerSpecificAlgebraicResidualEnvironment
