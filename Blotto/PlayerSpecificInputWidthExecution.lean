import Blotto.PlayerSpecificWidthExecution

/-! Actual coefficient-encoding measurement using the halving width routine.
No input height, width or aggregate-cost oracle is an executing argument. -/
namespace Blotto.PlayerSpecificInputWidthExecution
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights
set_option autoImplicit false
set_option maxHeartbeats 5000000

def scalar (model : RationalCostModel) (q : ℚ) : ℕ×ℕ :=
  let numerator := PlayerSpecificWidthExecution.run model q.num.natAbs
  let denominator := PlayerSpecificWidthExecution.run model q.den
  let combined := numerator.1+denominator.1
  (1+combined,numerator.2+denominator.2+16*rationalWordWidth q+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) numerator.1 denominator.1+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) 1 combined)

theorem scalar_value (model : RationalCostModel) (q : ℚ) : (scalar model q).1=rationalWordWidth q := by
  simp only [scalar,PlayerSpecificWidthExecution.value,rationalWordWidth,Nat.add_assoc]

def row (model : RationalCostModel) : Data → ℕ×ℕ
  | [] => (0,16)
  | q::p =>
    let head := scalar model q
    let tail := row model p
    (head.1+tail.1,head.2+tail.2+32*(1+binaryWordWidth (p.length+1))+
      GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) head.1 tail.1)

theorem row_value (model : RationalCostModel) (p : Data) : (row model p).1=RationalAggregateRecognitionCost.totalWidth p := by
  induction p with
  | nil => rfl
  | cons q p ih => simp only [row,scalar_value,ih,RationalAggregateRecognitionCost.totalWidth,List.map_cons,List.sum_cons]

def run (model : RationalCostModel) (p : Data) : ℕ×ℕ :=
  let measured := row model p
  (measured.1+1,measured.2+32*(1+binaryWordWidth p.length)+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) measured.1 1)

theorem value (model : RationalCostModel) (p : Data) :
    (run model p).1=PlayerSpecificRationalMagnitude.inputHeight p := by
  simp only [run,row_value,PlayerSpecificRationalMagnitude.inputHeight]

def width (H : ℕ) : ℕ := 128*(H+1)+128

theorem scalar_cost (model : RationalCostModel) (q : ℚ) (H : ℕ) (hq : RationalHeight q H) :
    (scalar model q).2≤1024*(H+1)*model.rat (width H) := by
  have hw:=rationalWordWidth_of_height hq
  have hn : binaryWordWidth q.num.natAbs≤1+2*H := by unfold rationalWordWidth at hw; omega
  have hd : binaryWordWidth q.den≤1+2*H := by unfold rationalWordWidth at hw; omega
  have hnp:=PlayerSpecificWidthExecution.price model q.num.natAbs
  have hdp:=PlayerSpecificWidthExecution.price model q.den
  have hNW : PlayerSpecificWidthExecution.width q.num.natAbs≤width H := by
    unfold PlayerSpecificWidthExecution.width width; omega
  have hDW : PlayerSpecificWidthExecution.width q.den≤width H := by
    unfold PlayerSpecificWidthExecution.width width; omega
  have hnm:=hnp.trans (Nat.mul_le_mul_left (128*(binaryWordWidth q.num.natAbs+1)) (model.monotone hNW))
  have hdm:=hdp.trans (Nat.mul_le_mul_left (128*(binaryWordWidth q.den+1)) (model.monotone hDW))
  let numerator := PlayerSpecificWidthExecution.run model q.num.natAbs
  let denominator := PlayerSpecificWidthExecution.run model q.den
  have hnv : numerator.1≤1+2*H := by rw [PlayerSpecificWidthExecution.value]; exact hn
  have hdv : denominator.1≤1+2*H := by rw [PlayerSpecificWidthExecution.value]; exact hd
  have word (n : ℕ) (hb : n≤4*H+4) : 1+binaryWordWidth n≤width H := by
    have hc:=PlayerSpecificRationalTrace.control_width n
    unfold width
    omega
  have ha := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a+b)
    numerator.1 denominator.1 (width H) (word _ (by omega)) (word _ (by omega)) (word _ (by omega))
  have hb := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a+b)
    1 (numerator.1+denominator.1) (width H) (word _ (by omega)) (word _ (by omega)) (word _ (by omega))
  have hcopy : rationalWordWidth q≤model.rat (width H) := hw.trans ((by unfold width; omega : 1+2*H≤width H).trans (model.word_le _))
  change numerator.2+denominator.2+16*rationalWordWidth q+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) numerator.1 denominator.1+
    GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) 1 (numerator.1+denominator.1)≤_
  nlinarith

end Blotto.PlayerSpecificInputWidthExecution
