import Blotto.PlayerSpecificCachedOverlapRowSourceCost

/-! Each overlap entry retains one decoded pair, one environment and
one computed weight/endpoint triple, with complete enclosing prices. -/
namespace Blotto.PlayerSpecificOverlapEntryExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run {k h : ℕ} (model : RationalCostModel) (root : Candidate) (first : Descriptor 3 k) (second : Descriptor 3 h)
    (interval budget : Data) (slot : Fin (k*h)) : (Data×(FixedArrayTable 4 Data×FixedArrayTable 4 Data))×ℕ :=
  let pair:=PlayerSpecificOverlapIndexExecution.run model k h slot
  let env:=PlayerSpecificOverlapEnvironmentExecution.run model root first second interval budget pair.1.1 pair.1.2
  let result:=PlayerSpecificCachedOverlapRowExecution.run model root env.1
  (result.1,pair.2+env.2+result.2+price model [.control 1])

theorem value {k h : ℕ} (model : RationalCostModel) (root : Candidate) (first : Descriptor 3 k) (second : Descriptor 3 h)
    (interval budget : Data) (slot : Fin (k*h)) :
    (run model root first second interval budget slot).1=PlayerSpecificAlgebraicOverlapTable.row model root
      (PlayerSpecificAlgebraicOverlapEnvironment.environment first second interval budget (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2) := by
  simp only [run,PlayerSpecificOverlapIndexExecution.value,PlayerSpecificOverlapEnvironmentExecution.value,PlayerSpecificCachedOverlapRowExecution.value]
theorem packing (model : RationalCostModel) : price model [.control 1]=2 := rfl
theorem price_equation {k h : ℕ} (model : RationalCostModel) (root : Candidate) (first : Descriptor 3 k) (second : Descriptor 3 h)
    (interval budget : Data) (slot : Fin (k*h)) :
    (run model root first second interval budget slot).2=(PlayerSpecificOverlapIndexExecution.run model k h slot).2+
      (PlayerSpecificOverlapEnvironmentExecution.run model root first second interval budget (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2).2+
      (PlayerSpecificCachedOverlapRowExecution.run model root (PlayerSpecificAlgebraicOverlapEnvironment.environment first second interval budget
        (finProdFinEquiv.symm slot).1 (finProdFinEquiv.symm slot).2)).2+2 := by
  simp only [run,PlayerSpecificOverlapIndexExecution.value,PlayerSpecificOverlapEnvironmentExecution.value,packing]

end Blotto.PlayerSpecificOverlapEntryExecution
