import Blotto.PlayerSpecificMixtureScalarSourceCost

/-! Complete binary descriptor assembly retains its complement and
each scaled weight once. Endpoint arrays and all returns are priced. -/
namespace Blotto.PlayerSpecificDescriptorBinaryExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run {N k m : ℕ} (model : RationalCostModel) (root : Candidate) (p : Data) (l : Descriptor N k) (r : Descriptor N m) : Descriptor N (k+m)×ℕ :=
  let complement:=PlayerSpecificMixtureScalarExecution.complement model root p
  let left:=FixedArrayTable.ofFn (fun slot => PlayerSpecificMixtureScalarExecution.scale model root p (l.weights.read slot))
  let right:=FixedArrayTable.ofFn (fun slot => PlayerSpecificMixtureScalarExecution.scale model root complement.1 (r.weights.read slot))
  let result:Descriptor N (k+m):=⟨FixedArrayTable.ofFn (Fin.addCases (fun slot => (left.read slot).1) (fun slot => (right.read slot).1)),
    FixedArrayTable.ofFn (Fin.addCases l.first.read r.first.read),FixedArrayTable.ofFn (Fin.addCases l.second.read r.second.read)⟩
  let env:=PlayerSpecificMixtureScalarExecution.oneEnvironment p
  (result,complement.2+(∑ slot : Fin k,(left.read slot).2)+(∑ slot : Fin m,(right.read slot).2)+
    price model (PlayerSpecificDescriptorProgramExecution.frame root env l)+
    price model (PlayerSpecificDescriptorProgramExecution.frame root env r)+
    price model (PlayerSpecificDescriptorProgramExecution.frame root env result)+price model (List.replicate 3 (.control 0)))

theorem value {N k m : ℕ} (model : RationalCostModel) (root : Candidate) (p : Data) (l : Descriptor N k) (r : Descriptor N m) :
    (run model root p l r).1=PlayerSpecificAlgebraicDescriptorBinary.binary root p l r := by
  simp only [run,FixedArrayTable.read_ofFn,PlayerSpecificMixtureScalarExecution.scale_value,
    PlayerSpecificMixtureScalarExecution.complement_value,PlayerSpecificAlgebraicDescriptorBinary.binary]

theorem packing (model : RationalCostModel) : price model (List.replicate 3 (.control 0))=6 := rfl

theorem price_equation {N k m : ℕ} (model : RationalCostModel) (root : Candidate) (p : Data) (l : Descriptor N k) (r : Descriptor N m) :
    (run model root p l r).2=(PlayerSpecificMixtureScalarExecution.complement model root p).2+
      (∑ slot : Fin k,(PlayerSpecificMixtureScalarExecution.scale model root p (l.weights.read slot)).2)+
      (∑ slot : Fin m,(PlayerSpecificMixtureScalarExecution.scale model root
        (PlayerSpecificMixtureScalarExecution.complement model root p).1 (r.weights.read slot)).2)+
      price model (PlayerSpecificDescriptorProgramExecution.frame root (PlayerSpecificMixtureScalarExecution.oneEnvironment p) l)+
      price model (PlayerSpecificDescriptorProgramExecution.frame root (PlayerSpecificMixtureScalarExecution.oneEnvironment p) r)+
      price model (PlayerSpecificDescriptorProgramExecution.frame root (PlayerSpecificMixtureScalarExecution.oneEnvironment p) (run model root p l r).1)+6 := by
  simp only [run,FixedArrayTable.read_ofFn,packing]

end Blotto.PlayerSpecificDescriptorBinaryExecution
