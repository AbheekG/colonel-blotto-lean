import Blotto.GeneralPaperSignedTailExecution

/-! All four accumulated native preparation counters are bounded by the
actual returned plan annotation. Its magnitude comes from native execution,
not an externally supplied metadata cap or a separate summation pass.
-/
namespace Blotto.GeneralPaperSignedTailOperands
open GeneralPaperUnsignedCellConstancy (Summary)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def magnitude (m k : ℕ) : ℕ := 1024*(m+2)*((35+k)+1)^2+512
def width (m k U : ℕ) : ℕ :=
  GeneralPaperRankArrayOperands.width (m+1) (35+k) (2*U)+256+32*binaryWordWidth (m+2)

def additions (primitive : ℕ → ℕ) (a b c d : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) a b+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (a+b) c+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (a+b+c) d+
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (a+b+c+d) 16

theorem word_bound (m k U : ℕ) : 1+binaryWordWidth (magnitude m k)≤width m k U := by
  have ha := binaryWordWidth_mul 1024 (m+2)
  have hb := binaryWordWidth_mul (1024*(m+2)) (((35+k)+1)^2)
  have hs := binaryWordWidth_mul ((35+k)+1) ((35+k)+1)
  rw [←pow_two] at hs
  have hd := GeneralPaperInitializerControlCounters.word_le_self ((35+k)+1)
  have hc := GeneralPaperRayOperandWidthEnvelope.word_add (1024*(m+2)*((35+k)+1)^2) 512
  have h1024 : binaryWordWidth 1024=11 := by decide
  have h512 : binaryWordWidth 512=10 := by decide
  unfold magnitude width GeneralPaperRankArrayOperands.width GeneralPaperRankOperands.width
  omega

theorem native_cap (m k : ℕ) :
    2*(m+1)*((35+k)*(12*(35+k)+34)+120)+88≤magnitude m k := by
  have hd : (35+k)*(12*(35+k)+34)+120≤128*((35+k)+1)^2 := by
    nlinarith only [Nat.zero_le k]
  have h := Nat.mul_le_mul_left (2*(m+1)) hd
  unfold magnitude
  nlinarith only [h,Nat.zero_le (((35+k)+1)^2)]

theorem annotation_bound {m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (W k U : ℕ) (summary : Summary k)
    (queries : FixedArrayTable m ℕ) :
    (GeneralPaperSignedTailExecution.run bits index primitive W k U summary queries).1.work≤magnitude m k := by
  rw [GeneralPaperSignedTailExecution.data]
  exact (GeneralPaperSignedTailPlan.prepare_work k U summary queries).trans (native_cap m k)

theorem additions_work {m : ℕ} (bits : Bool) (index primitive : ℕ → ℕ) (hMono : Monotone primitive)
    (W k U : ℕ) (summary : Summary k) (queries : FixedArrayTable m ℕ) :
    let pc := GeneralPaperSignedCutExecution.run bits index primitive W U false queries
    let nc := GeneralPaperSignedCutExecution.run bits index primitive W U true queries
    let pr := GeneralPaperRankArrayExecution.prepare bits index primitive W k summary pc.1.1
    let nr := GeneralPaperRankArrayExecution.prepare bits index primitive W k summary nc.1.1
    additions primitive pc.1.2 nc.1.2 pr.1.2 nr.1.2≤8*primitive (width m k U) := by
  let pc := GeneralPaperSignedCutExecution.run bits index primitive W U false queries
  let nc := GeneralPaperSignedCutExecution.run bits index primitive W U true queries
  let pr := GeneralPaperRankArrayExecution.prepare bits index primitive W k summary pc.1.1
  let nr := GeneralPaperRankArrayExecution.prepare bits index primitive W k summary nc.1.1
  have hWhole := annotation_bound bits index primitive W k U summary queries
  change pc.1.2+nc.1.2+pr.1.2+nr.1.2+16≤magnitude m k at hWhole
  change additions primitive pc.1.2 nc.1.2 pr.1.2 nr.1.2≤_
  have hWord := word_bound m k U
  have price (a b : ℕ) (ha : a≤magnitude m k) (hb : b≤magnitude m k) (hc : a+b≤magnitude m k) :
      GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) a b≤2*primitive (width m k U) :=
    (GeneralPaperNaturalPrimitivePrice.binary_le primitive hMono _ a b (magnitude m k) ha hb hc).trans
      (Nat.mul_le_mul_left 2 (hMono hWord))
  have ha := price pc.1.2 nc.1.2 (by omega) (by omega) (by omega)
  have hb := price (pc.1.2+nc.1.2) pr.1.2 (by omega) (by omega) (by omega)
  have hc := price (pc.1.2+nc.1.2+pr.1.2) nr.1.2 (by omega) (by omega) (by omega)
  have hd := price (pc.1.2+nc.1.2+pr.1.2+nr.1.2) 16 (by omega) (by omega) hWhole
  unfold additions
  omega

end Blotto.GeneralPaperSignedTailOperands
