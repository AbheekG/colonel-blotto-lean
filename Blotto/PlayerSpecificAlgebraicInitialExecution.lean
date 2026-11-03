import Blotto.PlayerSpecificAlgebraicPairLineage

/-! Priced executing initial field data. One sign call, one selected
division and three products consume shared constant/weighted/unit rows.
The scale inverse is a cached input computed once by the vector caller. -/
namespace Blotto.PlayerSpecificAlgebraicInitialExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificRationalTrace PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frame (root : Candidate) (inverseScale : Data) (v w : ℚ) (first second unit quotient : Data)
    (result : PlayerSpecificAlgebraicInitial.Result) : Trace :=
  copyRow root.polynomial++copyRow [root.interval.lo,root.interval.hi,v,w]++copyRow inverseScale++
    copyRow first++copyRow second++copyRow unit++copyRow quotient++copyRow result.length++
      copyRow result.initialA++copyRow result.initialB++[.control 1]

def run (model : RationalCostModel) (root : Candidate) (inverseScale : Data) (v w : ℚ) :
    PlayerSpecificAlgebraicInitial.Result×ℕ :=
  let negative:=scalar .multiply (-1) w
  let signed:=PlayerSpecificPolynomialSignExecution.run model root.polynomial [v,negative.1] root.interval
  let branch:=decide (signed.1≠.pos)
  let first:=PlayerSpecificFieldCombinationContract.constant root.polynomial v
  let second:=PlayerSpecificDivisionExecution.run [0,w] root.polynomial
  let unit:=PlayerSpecificFieldCombinationContract.constant root.polynomial 1
  let quotient:=if branch then PlayerSpecificFieldDivisionExecution.run model root.polynomial first.1 second.1.2 else
    PlayerSpecificFieldDivisionExecution.run model root.polynomial second.1.2 first.1
  let numerator:=if branch then first.1 else second.1.2
  let probabilityA:=if branch then quotient.1 else unit.1
  let probabilityB:=if branch then unit.1 else quotient.1
  let length:=PlayerSpecificModularExecution.run model root.polynomial inverseScale numerator
  let initialA:=PlayerSpecificModularExecution.run model root.polynomial length.1 probabilityA
  let initialB:=PlayerSpecificModularExecution.run model root.polynomial length.1 probabilityB
  let result:PlayerSpecificAlgebraicInitial.Result:=⟨length.1,initialA.1,initialB.1⟩
  (result,price model negative.2+signed.2+price model first.2+price model second.2+price model unit.2+
    quotient.2+length.2+initialA.2+initialB.2+price model (frame root inverseScale v w first.1 second.1.2 unit.1 quotient.1 result))

theorem value (model : RationalCostModel) (root : Candidate) (inverseScale : Data) (v w : ℚ) :
    (run model root inverseScale v w).1=PlayerSpecificAlgebraicInitial.run model root inverseScale v w := by
  simp only [run,scalar,Arithmetic.apply,neg_one_mul,
    PlayerSpecificFieldCombinationContract.constant_value,PlayerSpecificDivisionExecution.value,
    PlayerSpecificModularExecution.value]
  unfold PlayerSpecificAlgebraicInitial.run PlayerSpecificAlgebraicInitial.low PlayerSpecificAlgebraicInitial.weighted
    PlayerSpecificAlgebraicField.times PlayerSpecificAlgebraicReduction.reduce
  dsimp only
  split <;> simp only [PlayerSpecificFieldDivisionExecution.value]

end Blotto.PlayerSpecificAlgebraicInitialExecution
