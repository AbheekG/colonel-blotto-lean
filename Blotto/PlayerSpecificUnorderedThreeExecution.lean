import Blotto.PlayerSpecificOrderedThreeSourceCost

/-! Actual measured comparison-sort preparation. Only the selected
ordered input is prepared; swapped endpoints are restored from retained
outer rows, with all copies/indices and fixed dispatch packing priced. -/
namespace Blotto.PlayerSpecificUnorderedThreeExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicThreeInput
open PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def permuted (d : Descriptor 3 9) : Descriptor 3 9 :=
  ⟨d.weights,FixedArrayTable.ofFn (fun slot => let row:=d.first.read slot; FixedArrayTable.ofFn ![row.read 1,row.read 0,row.read 2]),
    FixedArrayTable.ofFn (fun slot => let row:=d.second.read slot; FixedArrayTable.ofFn ![row.read 1,row.read 0,row.read 2])⟩

def selected (model : RationalCostModel) (root : Candidate) (a : Input) (ordered : Bool) : Descriptor 3 9×ℕ :=
  if ordered then PlayerSpecificOrderedThreeExecution.run model root a else
    let result:=PlayerSpecificOrderedThreeExecution.run model root (PlayerSpecificAlgebraicUnorderedThree.swapped a)
    (permuted result.1,result.2)

def run (model : RationalCostModel) (root : Candidate) (a : Input) : Descriptor 3 9×ℕ :=
  let compared:=PlayerSpecificAlgebraicComparisonExecution.run model root a.first a.second
  let result:=selected model root a compared.1
  (result.1,compared.2+result.2+price model (PlayerSpecificDescriptorProgramExecution.frame root (PlayerSpecificThreeEnvironmentExecution.input a) result.1)+
    price model (List.replicate 6 (.control 1)))

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) :
    (run model root a).1=PlayerSpecificAlgebraicUnorderedThree.prepare model root a := by
  simp only [run,selected,PlayerSpecificAlgebraicComparisonExecution.value,PlayerSpecificAlgebraicUnorderedThree.prepare]
  split
  · exact PlayerSpecificOrderedThreeExecution.value model root a
  · rw [PlayerSpecificOrderedThreeExecution.value]
    rfl

theorem packing (model : RationalCostModel) : price model (List.replicate 6 (.control 1))=12 := by rfl

end Blotto.PlayerSpecificUnorderedThreeExecution
