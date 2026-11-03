import Blotto.PlayerSpecificSeparationExecution

/-! Complete separation-bound source price. The non-dyadic power exponent
is the actual certificate length at most seventeen; every word is derived. -/
namespace Blotto.PlayerSpecificSeparationCost
open PlayerSpecificNaturalExecution PlayerSpecificSeparationExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem run_cost (model : RationalCostModel) (M A B k : ℕ) (hk : k≤17) :
    (run model M A B k).2≤1000000*size M A B*model.rat (width M A B) := by
  let T:=size M A B
  let W:=width M A B
  have hT : 32≤T := by unfold T size; omega
  have hbase : binaryWordWidth M≤T := by unfold T size; omega
  have hA : A≤T := by unfold T size; omega
  have hB : B≤T := by unfold T size; omega
  have hOne : binaryWordWidth 1=1 := by decide
  have hTwo : binaryWordWidth 2=2 := by decide
  have hThree : binaryWordWidth 3=2 := by decide
  have hhalf:=words M A B k hk
  have htriple : binaryWordWidth (3*M)≤T+2 := by
    have h:=binaryWordWidth_mul 3 M
    omega
  have hderivative : binaryWordWidth (2^A*(1+3*M))≤2*T+5 := by
    have h:=binaryWordWidth_mul (2^A) (1+3*M)
    rw [PlayerSpecificIsolationDepthHeight.two_power_width] at h
    omega
  have hgrowth : binaryWordWidth ((1+M)^k)≤17*(T+2)+1 := by
    have h:=GeneralPaperNatPowerOperands.power_width (1+M) k
    have hm:=Nat.mul_le_mul_left k (hhalf.1.trans (by omega : binaryWordWidth M+2≤T+2))
    have hc:=Nat.mul_le_mul_right (T+2) hk
    omega
  have hbezout : binaryWordWidth (2^B*(1+M)^k)≤18*T+36 := by
    have h:=binaryWordWidth_mul (2^B) ((1+M)^k)
    rw [PlayerSpecificIsolationDepthHeight.two_power_width] at h
    omega
  have hpowerA := power_cost model 2 A
  have hpowerB := power_cost model 2 B
  have hpowerC := power_cost model (1+M) k
  have hwA : powerWidth 2 A≤W := by unfold powerWidth W width; rw [hTwo]; nlinarith
  have hwB : powerWidth 2 B≤W := by unfold powerWidth W width; rw [hTwo]; nlinarith
  have hwC : powerWidth (1+M) k≤W := by
    have hm:=Nat.mul_le_mul (show k+1≤18 by omega) (show binaryWordWidth (1+M)+1≤T+3 by omega)
    unfold powerWidth W width
    nlinarith
  have hpA:=hpowerA.trans (Nat.mul_le_mul_left (256*(A+1)) (model.monotone hwA))
  have hpB:=hpowerB.trans (Nat.mul_le_mul_left (256*(B+1)) (model.monotone hwB))
  have hpC:=hpowerC.trans (Nat.mul_le_mul_left (256*(k+1)) (model.monotone hwC))
  have small (n : ℕ) (h : binaryWordWidth n≤20*T+40) : 1+binaryWordWidth n≤W := by
    unfold W width
    omega
  have htr:=binary_cost model (fun a b => a*b) 3 M W (small _ (by omega)) (small _ (by omega)) (small _ (by omega))
  have hdf:=binary_cost model (fun a b => a+b) 1 (3*M) W (small _ (by omega)) (small _ (by omega)) (small _ (by omega))
  have hd:=binary_cost model (fun a b => a*b) (2^A) (1+3*M) W
    (small _ (by rw [PlayerSpecificIsolationDepthHeight.two_power_width]; omega)) (small _ (by omega)) (small _ (by omega))
  have hcf:=binary_cost model (fun a b => a+b) 1 M W (small _ (by omega)) (small _ (by omega)) (small _ (by omega))
  have hb:=binary_cost model (fun a b => a*b) (2^B) ((1+M)^k) W
    (small _ (by rw [PlayerSpecificIsolationDepthHeight.two_power_width]; omega)) (small _ (by omega)) (small _ (by omega))
  have hdprod:=binary_cost model (fun a b => a*b) (2^A*(1+3*M)) (2^B*(1+M)^k) W
    (small _ (by omega)) (small _ (by omega)) (small _ (by omega))
  have hmetaA:=PlayerSpecificRationalTrace.control_width A
  have hmetaB:=PlayerSpecificRationalTrace.control_width B
  have hmetak:=PlayerSpecificRationalTrace.control_width k
  have hword:=model.word_le W
  have hP : 1≤model.rat W := (by unfold W width; omega : 1≤W).trans hword
  have hproduct : binaryWordWidth ((2^A*(1+3*M))*(2^B*(1+M)^k))≤20*T := hhalf.2.2
  have hrecord : 32*(5+binaryWordWidth M+binaryWordWidth A+binaryWordWidth B+binaryWordWidth k+
      binaryWordWidth ((2^A*(1+3*M))*(2^B*(1+M)^k)))≤1024*T := by omega
  have hrecordP := hrecord.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (1024*T) hP)
  have hpA' := hpA.trans (Nat.mul_le_mul_right (model.rat W) (Nat.mul_le_mul_left 256 (Nat.add_le_add_right hA 1)))
  have hpB' := hpB.trans (Nat.mul_le_mul_right (model.rat W) (Nat.mul_le_mul_left 256 (Nat.add_le_add_right hB 1)))
  have hpC' := hpC.trans (Nat.mul_le_mul_right (model.rat W) (Nat.mul_le_mul_left 256 (show k+1≤18 by omega)))
  rw [run]
  simp only [binary_value,power_value]
  change _≤1000000*T*model.rat W
  nlinarith only [hpA',hpB',hpC',htr,hdf,hd,hcf,hb,hdprod,hrecordP,hT]

end Blotto.PlayerSpecificSeparationCost
