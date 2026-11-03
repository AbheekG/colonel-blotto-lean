import Blotto.PlayerSpecificInitialExecution

/-! Whole original-input root isolator. Polynomial and integer preparation
is executed once; cached rows and the computed depth feed the traversal.
All preparation, initial queries, conversion, draw records and output copies
are priced on this same return. -/
namespace Blotto.PlayerSpecificRootExecution
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem prepared_eq {p : Data} (cached : Prepared p) : cached=prepare p := by
  cases cached with
  | mk rows correct => subst rows; rfl

def run (model : RationalCostModel) (p : Data) : List Interval×ℕ :=
  let computed:=PlayerSpecificIntegerPreparation.run model p
  let cached : Prepared p:=⟨computed.1.polynomials.rows,(PlayerSpecificIntegerPreparation.polynomial_values model p).2.2⟩
  let initial:=PlayerSpecificInitialExecution.run cached computed.1.magnitude
  let isolated:=PlayerSpecificForestExecution.run cached computed.1.depth initial.1
  (isolated.1,computed.2+price model initial.2+price model isolated.2+
    64*(1+binaryWordWidth computed.1.magnitude)+price model (PlayerSpecificForestExecution.copyForest isolated.1)+
    32*(2+binaryWordWidth computed.1.depth+binaryWordWidth isolated.1.length))

theorem value (model : RationalCostModel) (p : Data) : (run model p).1=PlayerSpecificRootIsolation.run p := by
  simp only [run,PlayerSpecificForestExecution.value,PlayerSpecificInitialExecution.value,
    PlayerSpecificIntegerPreparation.depth_value,PlayerSpecificIntegerPreparation.magnitude_value,prepared_eq,
    PlayerSpecificRootIsolation.run,PlayerSpecificRootMagnitude.initial]

end Blotto.PlayerSpecificRootExecution
