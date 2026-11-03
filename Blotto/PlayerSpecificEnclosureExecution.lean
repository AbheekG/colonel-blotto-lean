import Blotto.PlayerSpecificNaturalExecution

/-! Root enclosure from the measured coefficient width, including executed
exponent arithmetic and every doubling/multiplication/control/return. -/
namespace Blotto.PlayerSpecificEnclosureExecution
open PlayerSpecificNaturalExecution
set_option autoImplicit false
set_option maxHeartbeats 5000000

def run (model : RationalCostModel) (H : ℕ) : ℕ×ℕ :=
  let doubled := binary model (fun a b => a*b) 2 H
  let exponent := binary model (fun a b => a+b) doubled.1 2
  let result := power model 2 exponent.1
  (result.1,doubled.2+exponent.2+result.2+32*(3+binaryWordWidth H+binaryWordWidth exponent.1+binaryWordWidth result.1))

theorem value (model : RationalCostModel) (H : ℕ) : (run model H).1=2^(2*H+2) := by
  simp only [run,binary,power_value]

def width (H : ℕ) : ℕ := 512*(H+1)

theorem run_cost (model : RationalCostModel) (H : ℕ) :
    (run model H).2≤4096*(H+1)*model.rat (width H) := by
  let L:=width H
  have word (n : ℕ) (hn : n≤2*H+2) : 1+binaryWordWidth n≤L := by
    have hb:=PlayerSpecificRationalTrace.control_width n
    unfold L width
    omega
  have hmul:=binary_cost model (fun a b => a*b) 2 H L (word _ (by omega)) (word _ (by omega)) (word _ (by omega))
  have hadd:=binary_cost model (fun a b => a+b) (2*H) 2 L (word _ (by omega)) (word _ (by omega)) (word _ (by omega))
  have hp:=power_cost model 2 (2*H+2)
  have h2 : binaryWordWidth 2=2 := by decide
  have hpowerW : powerWidth 2 (2*H+2)≤L := by unfold powerWidth L width; rw [h2]; omega
  have hpp:=hp.trans (Nat.mul_le_mul_left (256*(2*H+2+1)) (model.monotone hpowerW))
  have hresult : 1+binaryWordWidth (2^(2*H+2))≤L := by
    simp only [binaryWordWidth,Nat.log2_two_pow]
    unfold L width
    omega
  have hcopyH:=word H (by omega)
  have hcopyE:=word (2*H+2) (by omega)
  have hw:=model.word_le L
  change (binary model (fun a b => a*b) 2 H).2+
    (binary model (fun a b => a+b) (2*H) 2).2+(power model 2 (2*H+2)).2+
    32*(3+binaryWordWidth H+binaryWordWidth (2*H+2)+binaryWordWidth (power model 2 (2*H+2)).1)≤_
  rw [power_value]
  change _≤4096*(H+1)*model.rat L
  nlinarith

end Blotto.PlayerSpecificEnclosureExecution
