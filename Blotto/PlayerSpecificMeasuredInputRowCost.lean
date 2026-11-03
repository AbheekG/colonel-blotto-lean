import Blotto.PlayerSpecificMinimumOriginalSizes

/-! Complete original-input encoding measurement, without a fixed bound
on the number of coefficients. Aggregate word width pays for every
operand and all partial sums in the actual width routine. -/
namespace Blotto.PlayerSpecificMeasuredInputRowCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificInputWidthExecution
open RationalAggregateRecognitionCost
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem row_cost (model : RationalCostModel) (p : Data) (H : ℕ) (hp : HasHeight p H)
    (htotal : totalWidth p≤H) :
    (row model p).2≤2048*(p.length+1)*(H+1)*model.rat (width H) := by
  have hR : 1≤model.rat (width H) := (by unfold width; omega : 1≤width H).trans (model.word_le _)
  induction p with
  | nil => change 16≤2048*(0+1)*(H+1)*model.rat (width H); nlinarith only [hR]
  | cons q p ih =>
    have htail : totalWidth p≤H := by
      simp only [totalWidth,List.map_cons,List.sum_cons] at htotal ⊢
      omega
    have ht:=ih (tail_height hp) htail
    have hq:=scalar_cost model q H (head_height hp)
    have hhead : (scalar model q).1≤H := by
      rw [scalar_value]
      simp only [totalWidth,List.map_cons,List.sum_cons] at htotal
      omega
    have htailval : (row model p).1≤H := by rw [row_value]; exact htail
    have hlen : p.length+1≤H := (length_le_width _).trans htotal
    have word (n : ℕ) (hn : n≤2*H+1) : 1+binaryWordWidth n≤width H := by
      have hc:=PlayerSpecificRationalTrace.control_width n
      unfold width
      omega
    have ha:=GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a+b)
      (scalar model q).1 (row model p).1 (width H) (word _ (by omega)) (word _ (by omega)) (word _ (by omega))
    have hmeta : 1+binaryWordWidth (p.length+1)≤model.rat (width H) :=
      (word _ (by omega)).trans (model.word_le _)
    change (scalar model q).2+(row model p).2+32*(1+binaryWordWidth (p.length+1))+
      GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) (scalar model q).1 (row model p).1≤_
    simp only [List.length_cons]
    nlinarith only [ht,hq,ha,hmeta]

theorem source_cost (model : RationalCostModel) (p : Data) :
    (run model p).2≤4096*(p.length+1)*(PlayerSpecificRationalMagnitude.inputHeight p+1)*
      model.rat (width (PlayerSpecificRationalMagnitude.inputHeight p)) := by
  let H:=PlayerSpecificRationalMagnitude.inputHeight p
  have htotal : totalWidth p≤H := by unfold H PlayerSpecificRationalMagnitude.inputHeight; omega
  have hr:=row_cost model p H (input_height p) htotal
  have hlen : p.length≤H := (length_le_width p).trans htotal
  have hval : (row model p).1≤H := by rw [row_value]; exact htotal
  have word (n : ℕ) (hn : n≤H+1) : 1+binaryWordWidth n≤width H := by
    have hc:=PlayerSpecificRationalTrace.control_width n
    unfold width
    omega
  have ha:=GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a+b)
    (row model p).1 1 (width H) (word _ (by omega)) (word _ (by omega)) (word _ (by omega))
  have hmeta : 1+binaryWordWidth p.length≤model.rat (width H) := (word _ (by omega)).trans (model.word_le _)
  have hunit : model.rat (width H)≤(p.length+1)*(H+1)*model.rat (width H) := by
    have hp : 1≤(p.length+1)*(H+1) := Nat.mul_le_mul (by omega : 1≤p.length+1) (by omega : 1≤H+1)
    simpa only [one_mul] using Nat.mul_le_mul_right (model.rat (width H)) hp
  change (row model p).2+32*(1+binaryWordWidth p.length)+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) (row model p).1 1≤_
  nlinarith only [hr,ha,hmeta,hunit]

end Blotto.PlayerSpecificMeasuredInputRowCost
