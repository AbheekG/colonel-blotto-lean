import Blotto.PlayerSpecificInputWidthExecution

/-! Complete measured input-height price for the bounded coefficient lists
used by root preparation, including numerator and denominator scans. -/
namespace Blotto.PlayerSpecificInputWidthCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificInputWidthExecution
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem row_cost (model : RationalCostModel) (p : Data) (H : ℕ)
    (hp : HasHeight p H) (hlen : p.length≤17) :
    (row model p).2≤2048*(p.length+1)*(H+1)*model.rat (width H) := by
  have hW : 1≤model.rat (width H) := (by unfold width; omega : 1≤width H).trans (model.word_le _)
  induction p with
  | nil => change 16≤2048*(0+1)*(H+1)*model.rat (width H); nlinarith
  | cons q p ih =>
    have htl : p.length≤17 := by simp only [List.length_cons] at hlen; omega
    have ht := ih (tail_height hp) htl
    have hq := scalar_cost model q H (head_height hp)
    have hhead : (scalar model q).1≤1+2*H := by rw [scalar_value]; exact rationalWordWidth_of_height (head_height hp)
    have hsum := inputHeight_le (tail_height hp)
    have htail : (row model p).1≤17*(1+2*H) := by
      rw [row_value]
      unfold PlayerSpecificRationalMagnitude.inputHeight at hsum
      have hm:=Nat.mul_le_mul_right (1+2*H) htl
      omega
    have word (n : ℕ) (hn : n≤18*(1+2*H)+1) : 1+binaryWordWidth n≤width H := by
      have hb:=PlayerSpecificRationalTrace.control_width n
      unfold width
      omega
    have ha:=GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a+b)
      (scalar model q).1 (row model p).1 (width H) (word _ (by omega)) (word _ (by omega)) (word _ (by omega))
    have hmeta : 1+binaryWordWidth (p.length+1)≤model.rat (width H) :=
      (word _ (by omega)).trans (model.word_le _)
    change (scalar model q).2+(row model p).2+32*(1+binaryWordWidth (p.length+1))+
      GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) (scalar model q).1 (row model p).1≤_
    simp only [List.length_cons]
    nlinarith

theorem run_cost (model : RationalCostModel) (p : Data) (H : ℕ)
    (hp : HasHeight p H) (hlen : p.length≤17) :
    (run model p).2≤40000*(H+1)*model.rat (width H) := by
  have hr:=row_cost model p H hp hlen
  have hfactor:=Nat.mul_le_mul_right ((H+1)*model.rat (width H))
    (show 2048*(p.length+1)≤36864 by omega)
  have hrow : (row model p).2≤36864*(H+1)*model.rat (width H) := by nlinarith
  have hsum:=inputHeight_le hp
  have hv : (row model p).1≤17*(1+2*H) := by
    rw [row_value]
    unfold PlayerSpecificRationalMagnitude.inputHeight at hsum
    have hm:=Nat.mul_le_mul_right (1+2*H) hlen
    omega
  have word (n : ℕ) (hn : n≤17*(1+2*H)+1) : 1+binaryWordWidth n≤width H := by
    have hb:=PlayerSpecificRationalTrace.control_width n
    unfold width
    omega
  have ha:=GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a+b)
    (row model p).1 1 (width H) (word _ (by omega)) (word _ (by omega)) (word _ (by omega))
  have hmeta : 1+binaryWordWidth p.length≤model.rat (width H) := (word _ (by omega)).trans (model.word_le _)
  change (row model p).2+32*(1+binaryWordWidth p.length)+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) (row model p).1 1≤_
  nlinarith

end Blotto.PlayerSpecificInputWidthCost
