import Blotto.PlayerSpecificNestedTerminalEndpointExecution

/-! Complete terminal endpoint work derives its selected row size
from the original long/short/resource rows. No zero-test oracle runs. -/
namespace Blotto.PlayerSpecificNestedTerminalEndpointSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedTerminalInput PlayerSpecificAlgebraicNestedTerminalSizes
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (H : ℕ) : ℕ := PlayerSpecificAlgebraicEqualityCost.polynomialCoefficient*(H+1)^2+
  (1000*PlayerSpecificResourceCostProfile.rationalCoefficient)*(H+6)^3+6

theorem cost (root : Candidate) (a : Input) (j : Fin 3) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hH : 1≤H) (ha : Fits root a H) :
    (PlayerSpecificNestedTerminalEndpointExecution.run RationalCostModel.schoolbook root a j).2≤work H := by
  let model:=RationalCostModel.schoolbook
  let result:=(PlayerSpecificNestedTerminalEndpointExecution.run model root a j).1
  let env:=PlayerSpecificNestedTerminalEndpointExecution.environment a j
  let S:=H+5
  have hHS : H≤S := by dsimp [S]; omega
  have hout : Reduced root.polynomial result ∧ HasHeight result H := by
    change Reduced root.polynomial (PlayerSpecificNestedTerminalEndpointExecution.run model root a j).1 ∧
      HasHeight (PlayerSpecificNestedTerminalEndpointExecution.run model root a j).1 H
    rw [PlayerSpecificNestedTerminalEndpointExecution.value]
    exact endpoint_bounds root a H ha j
  have henv : ∀ k,Reduced root.polynomial (env.read k) ∧ HasHeight (env.read k) H := by
    intro k
    fin_cases k
    · simpa [env,PlayerSpecificNestedTerminalEndpointExecution.environment,FixedArrayTable.read_ofFn] using ha.long j
    · simpa [env,PlayerSpecificNestedTerminalEndpointExecution.environment,FixedArrayTable.read_ofFn] using ha.short j
    · simpa [env,PlayerSpecificNestedTerminalEndpointExecution.environment,FixedArrayTable.read_ofFn] using ha.resource j
  have ht:=PlayerSpecificAlgebraicEqualityCost.polynomial_cost root.polynomial (a.resource.read j) [] H hm hm0 hml
    (ha.resource j).1 (nil_reduced _ hm0) hmH (ha.resource j).2 (nil_height _) hH
  have hf:=PlayerSpecificExpressionVectorFrameCost.cost model root env (FixedArrayTable.ofFn (fun _ : Fin 1 => result)) S
    (mono hmH hHS) hml (mono he hHS)
    (fun k => ⟨mono (henv k).2 hHS,by have h:=(henv k).1.2; omega⟩)
    (by intro k; rw [FixedArrayTable.read_ofFn]; exact ⟨mono hout.2 hHS,by have h:=hout.1.2; omega⟩)
    (by dsimp [S]; omega) (by dsimp [S]; omega) (by dsimp [S]; omega)
  have hf':=hf.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 1000 S)
  rw [show S+1=H+6 by rfl] at hf'
  rw [PlayerSpecificNestedTerminalEndpointExecution.price_equation]
  exact Nat.add_le_add (Nat.add_le_add ht hf') (PlayerSpecificNestedTerminalEndpointExecution.packing_cost model j)

end Blotto.PlayerSpecificNestedTerminalEndpointSourceCost
