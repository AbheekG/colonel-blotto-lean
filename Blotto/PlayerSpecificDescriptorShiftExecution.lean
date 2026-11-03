import Blotto.PlayerSpecificDescriptorShiftRowSourceCost

/-! Complete measured descriptor shift. Each changed endpoint row is
retained once, and full input/output descriptor copies are priced. -/
namespace Blotto.PlayerSpecificDescriptorShiftExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def environment (s : Data) : FixedArrayTable 1 Data := FixedArrayTable.ofFn (fun _ => s)

def run {slots : ℕ} (model : RationalCostModel) (root : Candidate) (s : Data) (d : Descriptor 3 slots) : Descriptor 3 slots×ℕ :=
  let first:=FixedArrayTable.ofFn (fun slot => PlayerSpecificDescriptorShiftRowExecution.run model root s (d.first.read slot))
  let second:=FixedArrayTable.ofFn (fun slot => PlayerSpecificDescriptorShiftRowExecution.run model root s (d.second.read slot))
  let result:Descriptor 3 slots:=⟨d.weights,FixedArrayTable.ofFn (fun slot => (first.read slot).1),
    FixedArrayTable.ofFn (fun slot => (second.read slot).1)⟩
  (result,(∑ slot : Fin slots,(first.read slot).2)+(∑ slot : Fin slots,(second.read slot).2)+
    price model (PlayerSpecificDescriptorProgramExecution.frame root (environment s) d)+
    price model (PlayerSpecificDescriptorProgramExecution.frame root (environment s) result)+price model (List.replicate 3 (.control 0)))

theorem value {slots : ℕ} (model : RationalCostModel) (root : Candidate) (s : Data) (d : Descriptor 3 slots) :
    (run model root s d).1=PlayerSpecificAlgebraicDescriptorShift.shift root s d := by
  simp only [run,FixedArrayTable.read_ofFn,PlayerSpecificDescriptorShiftRowExecution.value,PlayerSpecificAlgebraicDescriptorShift.shift]

theorem packing (model : RationalCostModel) : price model (List.replicate 3 (.control 0))=6 := rfl

theorem price_equation {slots : ℕ} (model : RationalCostModel) (root : Candidate) (s : Data) (d : Descriptor 3 slots) :
    (run model root s d).2=(∑ slot : Fin slots,(PlayerSpecificDescriptorShiftRowExecution.run model root s (d.first.read slot)).2)+
      (∑ slot : Fin slots,(PlayerSpecificDescriptorShiftRowExecution.run model root s (d.second.read slot)).2)+
      price model (PlayerSpecificDescriptorProgramExecution.frame root (environment s) d)+
      price model (PlayerSpecificDescriptorProgramExecution.frame root (environment s) (run model root s d).1)+6 := by
  simp only [run,FixedArrayTable.read_ofFn,packing]

end Blotto.PlayerSpecificDescriptorShiftExecution
