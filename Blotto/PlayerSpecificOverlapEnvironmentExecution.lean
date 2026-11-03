import Blotto.PlayerSpecificOverlapIndexSourceCost

/-! An overlap environment caches each selected parent endpoint array
once and materializes all sixteen actual input rows with source frames. -/
namespace Blotto.PlayerSpecificOverlapEnvironmentExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def indices (k h : ℕ) (i : Fin k) (j : Fin h) : Trace :=
  PlayerSpecificAlgebraicCallerFrame.run [] [k,h,i.val,j.val,3,16,1]
def run {k h : ℕ} (model : RationalCostModel) (root : Candidate) (first : Descriptor 3 k) (second : Descriptor 3 h)
    (interval budget : Data) (i : Fin k) (j : Fin h) : FixedArrayTable 16 Data×ℕ :=
  let fp:=first.first.read i
  let fq:=first.second.read i
  let sp:=second.first.read j
  let sq:=second.second.read j
  let result:FixedArrayTable 16 Data:=FixedArrayTable.ofFn
    ![fp.read 0,fp.read 1,fp.read 2,fq.read 0,fq.read 1,fq.read 2,sp.read 0,sp.read 1,sp.read 2,
      sq.read 0,sq.read 1,sq.read 2,first.weights.read i,second.weights.read j,interval,budget]
  (result,price model (PlayerSpecificExpressionVectorExecution.frame root result result)+price model (indices k h i j))

theorem value {k h : ℕ} (model : RationalCostModel) (root : Candidate) (first : Descriptor 3 k) (second : Descriptor 3 h)
    (interval budget : Data) (i : Fin k) (j : Fin h) :
    (run model root first second interval budget i j).1=PlayerSpecificAlgebraicOverlapEnvironment.environment first second interval budget i j := rfl
theorem price_equation {k h : ℕ} (model : RationalCostModel) (root : Candidate) (first : Descriptor 3 k) (second : Descriptor 3 h)
    (interval budget : Data) (i : Fin k) (j : Fin h) :
    (run model root first second interval budget i j).2=
      price model (PlayerSpecificExpressionVectorExecution.frame root (run model root first second interval budget i j).1
        (run model root first second interval budget i j).1)+price model (indices k h i j) := by
  simp only [run]

end Blotto.PlayerSpecificOverlapEnvironmentExecution
