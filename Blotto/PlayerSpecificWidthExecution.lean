import Blotto.PlayerSpecificPolynomialPreparation
import Blotto.GeneralPaperDyadicPowerBits

/-! Binary length is computed by actual halving, not supplied by a width
oracle. Arithmetic, tests and all operand/result/control copies are priced. -/
namespace Blotto.PlayerSpecificWidthExecution
set_option autoImplicit false
set_option maxHeartbeats 5000000

def run (model : RationalCostModel) (n : ℕ) : ℕ×ℕ :=
  let tested := GeneralPaperIntegerWordPrice.compare model.rat n 2
  if n<2 then (1,16*(1+binaryWordWidth n)+tested) else
    let divided := n/2
    let rest := run model divided
    (rest.1+1,rest.2+32*(1+binaryWordWidth n)+tested+
      GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a/b) n 2+
      GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) rest.1 1)
termination_by n
decreasing_by omega

theorem value (model : RationalCostModel) (n : ℕ) : (run model n).1=binaryWordWidth n := by
  rw [run]
  split
  · rename_i hn
    change 1=n.log2+1
    rw [Nat.log2_def]
    split <;> omega
  · rename_i hn
    dsimp only
    rw [value model (n/2)]
    unfold binaryWordWidth
    rw [Nat.log2_def n]
    split <;> omega
termination_by n
decreasing_by omega

def width (n : ℕ) : ℕ := 4*binaryWordWidth n+16

theorem price (model : RationalCostModel) (n : ℕ) :
    (run model n).2≤128*(binaryWordWidth n+1)*model.rat (width n) := by
  let L := width n
  let P := model.rat L
  have hnword : 1+binaryWordWidth n≤L := by unfold L width; omega
  have hsmall (m : ℕ) (hm : m≤n) : 1+binaryWordWidth m≤L :=
    (Nat.add_le_add_left (binaryWordWidth_mono hm) 1).trans hnword
  have h2 : 1+binaryWordWidth 2≤L := by
    have he : binaryWordWidth 2=2 := by decide
    unfold L width
    omega
  have hcopy : 1+binaryWordWidth n≤P := hnword.trans (model.word_le L)
  have ht := GeneralPaperIntegerWordPrice.compare_le model.rat model.monotone n 2 L hnword h2
  rw [run]
  split
  · change 16*(1+binaryWordWidth n)+GeneralPaperIntegerWordPrice.compare model.rat n 2≤_
    change GeneralPaperIntegerWordPrice.compare model.rat n 2≤P at ht
    have hpos := binaryWordWidth_pos n
    nlinarith
  · rename_i hlarge
    have hdiv := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a/b)
      n 2 L hnword h2 (hsmall (n/2) (Nat.div_le_self n 2))
    have hrec := price model (n/2)
    have hmono : width (n/2)≤L := by
      have hm:=binaryWordWidth_mono (Nat.div_le_self n 2)
      unfold L width
      omega
    have hrecp := hrec.trans (Nat.mul_le_mul_left (128*(binaryWordWidth (n/2)+1)) (model.monotone hmono))
    have hv:=value model (n/2)
    have hdepth : binaryWordWidth n=binaryWordWidth (n/2)+1 := by
      unfold binaryWordWidth
      rw [Nat.log2_def n]
      split <;> omega
    have hrv : (run model (n/2)).1≤binaryWordWidth n := by omega
    have hrr : 1+binaryWordWidth (run model (n/2)).1≤L := by
      have h:=PlayerSpecificRationalTrace.control_width (run model (n/2)).1
      unfold L width
      omega
    have h1 : 1+binaryWordWidth 1≤L := by
      have he : binaryWordWidth 1=1 := by decide
      unfold L width
      omega
    have hout : 1+binaryWordWidth ((run model (n/2)).1+1)≤L := by
      have h:=PlayerSpecificRationalTrace.control_width ((run model (n/2)).1+1)
      unfold L width
      omega
    have hadd := GeneralPaperIntegerWordPrice.natural_binary model.rat model.monotone (fun a b => a+b)
      (run model (n/2)).1 1 L hrr h1 hout
    change _≤2*P at hdiv hadd
    change GeneralPaperIntegerWordPrice.compare model.rat n 2≤P at ht
    change (run model (n/2)).2+32*(1+binaryWordWidth n)+GeneralPaperIntegerWordPrice.compare model.rat n 2+
      GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a/b) n 2+
      GeneralPaperNaturalPrimitivePrice.binary model.rat (fun a b => a+b) (run model (n/2)).1 1≤_
    change (run model (n/2)).2≤128*(binaryWordWidth (n/2)+1)*P at hrecp
    change _≤128*(binaryWordWidth n+1)*P
    nlinarith only [hrecp,hdiv,hadd,ht,hcopy,hdepth]
termination_by n
decreasing_by omega

end Blotto.PlayerSpecificWidthExecution
