import Blotto.PlayerSpecificOverlapEntrySourceCost

/-! Complete measured overlap-table materialization. The slot count
executes once; every pair/environment/row executes once and all final
weight/endpoint arrays read the retained entry results. -/
namespace Blotto.PlayerSpecificOverlapTableExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def scalars (interval budget : Data) : FixedArrayTable 2 Data := FixedArrayTable.ofFn ![interval,budget]
def run {k h : ℕ} (model : RationalCostModel) (root : Candidate) (first : Descriptor 3 k) (second : Descriptor 3 h)
    (interval budget : Data) : Descriptor 4 (k*h)×ℕ :=
  let count:=PlayerSpecificNaturalExecution.binary model (fun a b => a*b) k h
  let rows:=FixedArrayTable.ofFn (fun slot : Fin count.1 => PlayerSpecificOverlapEntryExecution.run model root first second interval budget slot)
  let result:Descriptor 4 count.1:=⟨FixedArrayTable.ofFn (fun slot => (rows.read slot).1.1),
    FixedArrayTable.ofFn (fun slot => (rows.read slot).1.2.1),FixedArrayTable.ofFn (fun slot => (rows.read slot).1.2.2)⟩
  let env:=scalars interval budget
  (result,count.2+(∑ slot : Fin count.1,(rows.read slot).2)+
    price model (PlayerSpecificDescriptorProgramExecution.frame root env first)+
    price model (PlayerSpecificDescriptorProgramExecution.frame root env second)+
    price model (PlayerSpecificDescriptorProgramExecution.frame root env result)+price model (List.replicate 3 (.control 1)))

theorem value {k h : ℕ} (model : RationalCostModel) (root : Candidate) (first : Descriptor 3 k) (second : Descriptor 3 h)
    (interval budget : Data) :
    (run model root first second interval budget).1=PlayerSpecificAlgebraicOverlapTable.prepare model root first second interval budget := by
  dsimp only [run,PlayerSpecificNaturalExecution.binary]
  simp only [FixedArrayTable.read_ofFn,PlayerSpecificOverlapEntryExecution.value,PlayerSpecificAlgebraicOverlapTable.prepare]
theorem packing (model : RationalCostModel) : price model (List.replicate 3 (.control 1))=6 := rfl

theorem price_equation {k h : ℕ} (model : RationalCostModel) (root : Candidate) (first : Descriptor 3 k) (second : Descriptor 3 h)
    (interval budget : Data) :
    (run model root first second interval budget).2=(PlayerSpecificNaturalExecution.binary model (fun a b => a*b) k h).2+
      (∑ slot : Fin (k*h),(PlayerSpecificOverlapEntryExecution.run model root first second interval budget slot).2)+
      price model (PlayerSpecificDescriptorProgramExecution.frame root (scalars interval budget) first)+
      price model (PlayerSpecificDescriptorProgramExecution.frame root (scalars interval budget) second)+
      price model (PlayerSpecificDescriptorProgramExecution.frame root (scalars interval budget) (run model root first second interval budget).1)+6 := by
  dsimp only [run,PlayerSpecificNaturalExecution.binary]
  simp only [FixedArrayTable.read_ofFn,packing]
  rfl

end Blotto.PlayerSpecificOverlapTableExecution
