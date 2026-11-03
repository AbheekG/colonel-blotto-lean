import Blotto.PlayerSpecificAlgebraicUnorderedThree

/-! The executed raw-input geometry transformation has three fixed
arithmetic layers, covering all original input rows and constant one. -/
namespace Blotto.PlayerSpecificAlgebraicThreeEnvironmentSizes
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicThreeInput
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Fits (root : Candidate) (a : Input) (T : ℕ) : Prop where
  budget : Reduced root.polynomial a.budget ∧ HasHeight a.budget T
  first : Reduced root.polynomial a.first ∧ HasHeight a.first T
  second : Reduced root.polynomial a.second ∧ HasHeight a.second T
  third : Reduced root.polynomial a.third ∧ HasHeight a.third T
  probability : Reduced root.polynomial a.probability ∧ HasHeight a.probability T

theorem iterate_add (a b T : ℕ) : iterate a (iterate b T)=iterate (a+b) T := by
  induction a with
  | zero => rw [Nat.zero_add]; rfl
  | succ a ih => simp only [Nat.succ_add,iterate,ih]

theorem environment_height (root : Candidate) (a : Input) (T : ℕ) (hfit : Fits root a T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (hT : 1≤T) :
    ∀ j,HasHeight ((environment root a).read j) (iterate 3 T) := by
  have hstep : T+T+1≤step T := by
    have h:=calibrate 3 T (by unfold PlayerSpecificAlgebraicHeightEnvelope.coefficient; omega)
    omega
  have h13 : step T≤ iterate 3 T := PlayerSpecificAlgebraicExpressionBudget.fuel_mono T (show 1≤3 by omega)
  have hb : ∀ row,Reduced root.polynomial row → HasHeight row T →
      HasHeight (PlayerSpecificAlgebraicField.minus root.polynomial a.budget row) (iterate 3 T) := by
    intro row hr hh
    exact mono (PlayerSpecificShortReduction.minus_height _ _ _ hm hm0 hfit.budget.1 hr T T hfit.budget.2 hh)
      (hstep.trans h13)
  have hunit:=constant_height root.polynomial 1 T hmT (one_height.mono hT) hT hml
  have huRed:=PlayerSpecificAlgebraicField.constant_reduced root.polynomial 1 hm hm0
  have hbase : T≤step T := (Nat.le_succ _).trans (large T)
  have hcomp:=PlayerSpecificShortReduction.minus_height root.polynomial _ a.probability hm hm0 huRed hfit.probability.1
    (step T) (step T) hunit (mono hfit.probability.2 hbase)
  have hshort : step T+step T+1≤step (step T) := by
    have h:=calibrate 3 (step T) (by unfold PlayerSpecificAlgebraicHeightEnvelope.coefficient; omega)
    omega
  have hT2 : T≤step (step T) := PlayerSpecificAlgebraicExpressionBudget.initial_le 2 T
  have hh:=times_height root.polynomial a.third
    (PlayerSpecificAlgebraicField.minus root.polynomial (PlayerSpecificAlgebraicField.constant root.polynomial 1) a.probability)
    (step (step T)) hm hm0 hml hfit.third.1 (PlayerSpecificAlgebraicField.minus_reduced _ _ _ hm hm0)
    (mono hmT hT2) (mono hfit.third.2 hT2) (mono hcomp hshort)
  intro j
  fin_cases j <;> simp only [environment,FixedArrayTable.read_ofFn]
  · exact hb a.first hfit.first.1 hfit.first.2
  · exact hb a.second hfit.second.1 hfit.second.2
  · exact hb a.third hfit.third.1 hfit.third.2
  · exact hh

theorem swapped (root : Candidate) (a : Input) (T : ℕ) (h : Fits root a T) :
    Fits root (PlayerSpecificAlgebraicUnorderedThree.swapped a) T :=
  ⟨h.budget,h.second,h.first,h.third,h.probability⟩

end Blotto.PlayerSpecificAlgebraicThreeEnvironmentSizes
