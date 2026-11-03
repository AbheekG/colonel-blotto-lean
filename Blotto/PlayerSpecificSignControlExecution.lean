import Blotto.PlayerSpecificSignLinearSizes

/-! Actual integer sign controls. All powers/products/width measurements
execute with operand-sized source prices; callers supply measured row widths
and actual row lengths, not an externally chosen precision. -/
namespace Blotto.PlayerSpecificSignControlExecution
set_option autoImplicit false
set_option maxHeartbeats 2000000

structure Result where
  magnitude : ℕ
  enlarged : ℕ
  elementPower : ℕ
  certificatePower : ℕ
  lipschitz : ℕ
  gap : ℕ
  operand : ℕ
  depth : ℕ

def words (r : Result) : List ℕ :=
  [r.magnitude,r.enlarged,r.elementPower,r.certificatePower,r.lipschitz,r.gap,r.operand,r.depth]
def copy (r : Result) : ℕ := 64*((words r).map (fun n => 1+binaryWordWidth n)).sum
def inputs (endpointHeight elementHeight certificateHeight elementLength certificateLength : ℕ) : List ℕ :=
  [endpointHeight,elementHeight,certificateHeight,elementLength,certificateLength]

def run (model : RationalCostModel) (endpointHeight elementHeight certificateHeight elementLength certificateLength : ℕ) : Result×ℕ :=
  let M:=PlayerSpecificNaturalExecution.power model 2 endpointHeight
  let enlarged:=PlayerSpecificNaturalExecution.binary model (fun x y => x+y) 1 M.1
  let elementPower:=PlayerSpecificNaturalExecution.power model 2 elementHeight
  let certificatePower:=PlayerSpecificNaturalExecution.power model 2 certificateHeight
  let intervalElementPower:=PlayerSpecificNaturalExecution.power model enlarged.1 elementLength
  let intervalCertificatePower:=PlayerSpecificNaturalExecution.power model enlarged.1 certificateLength
  let elementCoefficient:=PlayerSpecificNaturalExecution.binary model (fun x y => x*y) elementLength elementPower.1
  let elementProduct:=PlayerSpecificNaturalExecution.binary model (fun x y => x*y) elementCoefficient.1 intervalElementPower.1
  let lipschitz:=PlayerSpecificNaturalExecution.binary model (fun x y => x+y) 1 elementProduct.1
  let gap:=PlayerSpecificNaturalExecution.binary model (fun x y => x*y) certificatePower.1 intervalCertificatePower.1
  let eightM:=PlayerSpecificNaturalExecution.binary model (fun x y => x*y) 8 M.1
  let scaled:=PlayerSpecificNaturalExecution.binary model (fun x y => x*y) eightM.1 lipschitz.1
  let operand:=PlayerSpecificNaturalExecution.binary model (fun x y => x*y) scaled.1 gap.1
  let depth:=PlayerSpecificWidthExecution.run model operand.1
  let result:Result:=⟨M.1,enlarged.1,elementPower.1,certificatePower.1,lipschitz.1,gap.1,operand.1,depth.1⟩
  (result,M.2+enlarged.2+elementPower.2+certificatePower.2+intervalElementPower.2+intervalCertificatePower.2+
    elementCoefficient.2+elementProduct.2+lipschitz.2+gap.2+eightM.2+scaled.2+operand.2+depth.2+copy result+
    64*((inputs endpointHeight elementHeight certificateHeight elementLength certificateLength).map
      (fun n => 1+binaryWordWidth n)).sum)

theorem values (model : RationalCostModel) (E A B na nb : ℕ) :
    let r:=(run model E A B na nb).1
    r.magnitude=2^E ∧ r.enlarged=1+2^E ∧ r.elementPower=2^A ∧ r.certificatePower=2^B ∧
      r.lipschitz=1+na*2^A*(1+2^E)^na ∧ r.gap=2^B*(1+2^E)^nb ∧
      r.operand=8*2^E*(1+na*2^A*(1+2^E)^na)*(2^B*(1+2^E)^nb) ∧
      r.depth=binaryWordWidth (8*2^E*(1+na*2^A*(1+2^E)^na)*(2^B*(1+2^E)^nb)) := by
  simp only [run,PlayerSpecificNaturalExecution.power_value,PlayerSpecificNaturalExecution.binary_value,
    PlayerSpecificWidthExecution.value,and_self]

end Blotto.PlayerSpecificSignControlExecution
