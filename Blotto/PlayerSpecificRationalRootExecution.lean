import Blotto.PlayerSpecificRationalRootRowsCost

/-! Whole original-input rational-root enumeration. Polynomial/integer
preparation is cached once; the computed longer forest feeds at most three
actual CF queries, signed decodes and exact acceptance calls. -/
namespace Blotto.PlayerSpecificRationalRootExecution
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem rows_correct (model : RationalCostModel) (p : Data) :
    (PlayerSpecificReconstructionCache.run model p).1.isolation.polynomials.rows=PlayerSpecificSturmRootCount.rows p := by
  rw [PlayerSpecificReconstructionCache.isolation_value]
  exact (PlayerSpecificIntegerPreparation.polynomial_values model p).2.2

def run (model : RationalCostModel) (p : Data) : Data×ℕ :=
  let computed:=PlayerSpecificReconstructionCache.run model p
  let cache:=computed.1
  let prepared : Prepared p:=⟨cache.isolation.polynomials.rows,rows_correct model p⟩
  let initial:=PlayerSpecificInitialExecution.run prepared cache.isolation.magnitude
  let forest:=PlayerSpecificForestExecution.run prepared cache.depth initial.1
  let result:=PlayerSpecificRationalRootRows.run model p cache forest.1
  (result.1,computed.2+price model initial.2+price model forest.2+result.2+
    64*(1+binaryWordWidth cache.isolation.magnitude)+price model (copyRow result.1)+32*cache.word)

theorem value (model : RationalCostModel) (p : Data) : (run model p).1=PlayerSpecificRationalRoots.run p := by
  simp only [run,PlayerSpecificRationalRootRows.value,PlayerSpecificForestExecution.value,
    PlayerSpecificInitialExecution.value,PlayerSpecificReconstructionLeafBounds.magnitude_value,
    PlayerSpecificReconstructionCache.depth_value,PlayerSpecificRootExecution.prepared_eq,
    PlayerSpecificRationalRoots.run,PlayerSpecificRationalRoots.intervals,PlayerSpecificRootMagnitude.initial]

end Blotto.PlayerSpecificRationalRootExecution
