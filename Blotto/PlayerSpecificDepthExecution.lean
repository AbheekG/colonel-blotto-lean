import Blotto.PlayerSpecificSeparationCost

/-! Computed separation denominator and isolation depth, including both
integer products and an actual halving scan of the resulting word. -/
namespace Blotto.PlayerSpecificDepthExecution
open PlayerSpecificNaturalExecution PlayerSpecificSeparationExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000

def run (model : RationalCostModel) (M A B k : ℕ) : (ℕ×ℕ)×ℕ :=
  let separated := PlayerSpecificSeparationExecution.run model M A B k
  let doubled := binary model (fun a b => a*b) 2 M
  let product := binary model (fun a b => a*b) doubled.1 separated.1
  let measured := PlayerSpecificWidthExecution.run model product.1
  ((separated.1,measured.1),separated.2+doubled.2+product.2+measured.2+
    32*(3+binaryWordWidth M+binaryWordWidth separated.1+binaryWordWidth measured.1))

theorem values (model : RationalCostModel) (M A B k : ℕ) :
    (run model M A B k).1.1=(2^A*(1+3*M))*(2^B*(1+M)^k) ∧
      (run model M A B k).1.2=binaryWordWidth (2*M*((2^A*(1+3*M))*(2^B*(1+M)^k))) := by
  simp only [run,PlayerSpecificSeparationExecution.value,binary_value,PlayerSpecificWidthExecution.value,and_self]

theorem run_cost (model : RationalCostModel) (M A B k : ℕ) (hk : k≤17) :
    (run model M A B k).2≤2000000*size M A B*model.rat (width M A B) := by
  let T:=size M A B
  let W:=width M A B
  let D:=(2^A*(1+3*M))*(2^B*(1+M)^k)
  have hT : 32≤T := by unfold T size; omega
  have hM : binaryWordWidth M≤T := by unfold T size; omega
  have hD : binaryWordWidth D≤20*T := (words M A B k hk).2.2
  have h2 : binaryWordWidth 2=2 := by decide
  have htwoM : binaryWordWidth (2*M)≤T+2 := by have h:=binaryWordWidth_mul 2 M; omega
  have hproduct : binaryWordWidth (2*M*D)≤21*T+2 := by have h:=binaryWordWidth_mul (2*M) D; omega
  have hw : PlayerSpecificWidthExecution.width (2*M*D)≤W := by
    unfold PlayerSpecificWidthExecution.width W width
    omega
  have hp:=PlayerSpecificWidthExecution.price model (2*M*D)
  have hpp:=hp.trans (Nat.mul_le_mul_left (128*(binaryWordWidth (2*M*D)+1)) (model.monotone hw))
  have hpc:=hpp.trans (Nat.mul_le_mul_right (model.rat W) (Nat.mul_le_mul_left 128 (show binaryWordWidth (2*M*D)+1≤21*T+3 by omega)))
  have small (n : ℕ) (hn : binaryWordWidth n≤21*T+4) : 1+binaryWordWidth n≤W := by unfold W width; omega
  have ht:=binary_cost model (fun a b => a*b) 2 M W (small _ (by omega)) (small _ (by omega)) (small _ (by omega))
  have hm:=binary_cost model (fun a b => a*b) (2*M) D W (small _ (by omega)) (small _ (by omega)) (small _ (by omega))
  have hsep:=PlayerSpecificSeparationCost.run_cost model M A B k hk
  have hmeasure:=PlayerSpecificRationalTrace.control_width (binaryWordWidth (2*M*D))
  have hrecord : 32*(3+binaryWordWidth M+binaryWordWidth D+binaryWordWidth (binaryWordWidth (2*M*D)))≤2048*T := by omega
  have hW:=model.word_le W
  have hP : 1≤model.rat W := (by unfold W width; omega : 1≤W).trans hW
  have hrp:=hrecord.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2048*T) hP)
  rw [run]
  simp only [PlayerSpecificSeparationExecution.value,binary_value,PlayerSpecificWidthExecution.value]
  change (PlayerSpecificSeparationExecution.run model M A B k).2+
    (binary model (fun a b => a*b) 2 M).2+(binary model (fun a b => a*b) (2*M) D).2+
    (PlayerSpecificWidthExecution.run model (2*M*D)).2+
    32*(3+binaryWordWidth M+binaryWordWidth D+binaryWordWidth (binaryWordWidth (2*M*D)))≤2000000*T*model.rat W
  change (PlayerSpecificSeparationExecution.run model M A B k).2≤1000000*T*model.rat W at hsep
  have hTP:=Nat.mul_le_mul_right (model.rat W) hT
  nlinarith only [hsep,hpc,ht,hm,hrp,hTP]

end Blotto.PlayerSpecificDepthExecution
