import Blotto.PlayerSpecificInitialLineageBound

/-! Computable pairwise resource rounding in the retained number field.
Two cached exact comparisons choose endpoint/residual formulas. The coin
probability is used only for the lottery and never fed into resource rows. -/
namespace Blotto.PlayerSpecificAlgebraicPairStep
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificSturmVariations PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def le (model : RationalCostModel) (root : Candidate) (a b : Data) : Bool :=
  decide ((PlayerSpecificPolynomialSignExecution.run model root.polynomial (subtract a b) root.interval).1≠.pos)

structure Result where
  total : Data
  upperA : Data
  upperB : Data
  lowerA : Data
  lowerB : Data
  probability : Data

def run (model : RationalCostModel) (root : Candidate) (lengthA lengthB a b : Data) : Result :=
  let m:=root.polynomial
  let total:=PlayerSpecificAlgebraicField.plus m a b
  let lowA:=le model root total lengthA
  let lowB:=le model root total lengthB
  let upperA:=if lowA then total else lengthA
  let upperB:=if lowA then [] else PlayerSpecificAlgebraicField.minus m total lengthA
  let lowerA:=if lowB then [] else PlayerSpecificAlgebraicField.minus m total lengthB
  let lowerB:=if lowB then total else lengthB
  let numerator:=PlayerSpecificAlgebraicField.minus m a lowerA
  let denominator:=PlayerSpecificAlgebraicField.minus m upperA lowerA
  ⟨total,upperA,upperB,lowerA,lowerB,PlayerSpecificAlgebraicField.divide m numerator denominator⟩

theorem le_correct (model : RationalCostModel) (root : Candidate) (a b : Data)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ) (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) :
    le model root a b=true ↔ realEvaluate a x≤realEvaluate b x := by
  have hs:=PlayerSpecificPolynomialSignExecution.correct model root.polynomial (subtract a b) root.interval hm hirr hv x hx
  simp only [le,decide_eq_true_eq,hs,real_subtract,SignType.pos_eq_one,ne_eq,sign_eq_one_iff,not_lt,sub_nonpos]

theorem reduced (model : RationalCostModel) (root : Candidate) (lengthA lengthB a b : Data)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hA : Reduced root.polynomial lengthA) (hB : Reduced root.polynomial lengthB) :
    let r:=run model root lengthA lengthB a b
    Reduced root.polynomial r.total ∧ Reduced root.polynomial r.upperA ∧ Reduced root.polynomial r.upperB ∧
      Reduced root.polynomial r.lowerA ∧ Reduced root.polynomial r.lowerB ∧ Reduced root.polynomial r.probability := by
  have ht:=PlayerSpecificAlgebraicField.plus_reduced root.polynomial a b hm hm0
  have hz:=nil_reduced root.polynomial hm0
  have hu:=PlayerSpecificAlgebraicField.minus_reduced root.polynomial (PlayerSpecificAlgebraicField.plus root.polynomial a b) lengthA hm hm0
  have hl:=PlayerSpecificAlgebraicField.minus_reduced root.polynomial (PlayerSpecificAlgebraicField.plus root.polynomial a b) lengthB hm hm0
  dsimp only [run]
  split <;> split <;> exact ⟨ht,by assumption,by assumption,by assumption,by assumption,
    PlayerSpecificAlgebraicField.divide_reduced _ _ _ hm hm0⟩

end Blotto.PlayerSpecificAlgebraicPairStep
