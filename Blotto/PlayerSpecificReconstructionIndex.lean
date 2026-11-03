import Blotto.PlayerSpecificReconstructionCacheCost

/-! Actual affine dyadic-cell index: rational normalization/multiplication,
canonical numerator/denominator extraction and natural quotient. All cast,
read, arithmetic and returned-word copies are priced. -/
namespace Blotto.PlayerSpecificReconstructionIndex
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 5000000

def run (model : RationalCostModel) (M C : ℕ) (node : Interval) : ℕ×ℕ :=
  let shifted:=scalar .add node.lo (M:ℚ)
  let span:=scalar .multiply 2 (M:ℚ)
  let normalized:=scalar .divide shifted.1 span.1
  let located:=scalar .multiply (C:ℚ) normalized.1
  let quotient:=PlayerSpecificNaturalExecution.binary model (fun a b => a/b) located.1.num.toNat located.1.den
  (quotient.1,price model (shifted.2++span.2++normalized.2++located.2)+quotient.2+
    64*(5+binaryWordWidth M+binaryWordWidth C+binaryWordWidth located.1.num.natAbs+
      binaryWordWidth located.1.den+binaryWordWidth quotient.1))

theorem value (model : RationalCostModel) (M C : ℕ) (node : Interval) :
    (run model M C node).1=PlayerSpecificRootCells.index M C node := by
  simp only [run,scalar,Arithmetic.apply,PlayerSpecificNaturalExecution.binary_value,PlayerSpecificRootCells.index,PlayerSpecificRootCells.normalized]

theorem natural_height (n T : ℕ) (hT : 1≤T) (hn : binaryWordWidth n≤T) : RationalHeight (n:ℚ) T := by
  have hnum:=(lt_pow_binaryWordWidth n).trans_le (Nat.pow_le_pow_right (by decide) hn)
  have htwo : 2≤2^T := by simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hT
  simp only [RationalHeight,Rat.num_natCast,Rat.den_natCast,Int.natAbs_natCast]
  exact ⟨hnum,by omega⟩

theorem run_cost (model : RationalCostModel) (M C : ℕ) (node : Interval) (T : ℕ)
    (hT : 2≤T) (hlo : RationalHeight node.lo T) (hM : binaryWordWidth M≤T) (hC : binaryWordWidth C≤T) :
    (run model M C node).2≤5000*model.rat (32*(T+1)) := by
  let W:=32*(T+1)
  let shifted:=scalar .add node.lo (M:ℚ)
  let span:=scalar .multiply 2 (M:ℚ)
  let normalized:=scalar .divide shifted.1 span.1
  let located:=scalar .multiply (C:ℚ) normalized.1
  let quotient:=PlayerSpecificNaturalExecution.binary model (fun a b => a/b) located.1.num.toNat located.1.den
  have hMh:=natural_height M T (by omega) hM
  have hCh:=natural_height C T (by omega) hC
  have htwo : RationalHeight (2:ℚ) 2 := by norm_num [RationalHeight]
  have hs : RationalHeight shifted.1 (2*T+1) := by simpa only [shifted,scalar,Arithmetic.apply,two_mul] using hlo.add hMh
  have hspan : RationalHeight span.1 (T+2) := by simpa only [span,scalar,Arithmetic.apply,Nat.add_comm] using htwo.mul hMh
  have hn : RationalHeight normalized.1 (3*T+3) := by
    simpa only [normalized,scalar,Arithmetic.apply,show (2*T+1)+(T+2)=3*T+3 by omega] using hs.div hspan
  have hl : RationalHeight located.1 (4*T+3) := by
    simpa only [located,scalar,Arithmetic.apply,show T+(3*T+3)=4*T+3 by omega] using hCh.mul hn
  have hcommon : ∀ q : ℚ,RationalHeight q (4*T+3) → rationalWordWidth q≤W := by
    intro q hq
    exact (rationalWordWidth_of_height hq).trans (by unfold W; omega)
  have scalar_bound (op : Arithmetic) (a b : ℚ) (ha : RationalHeight a (4*T+3))
      (hb : RationalHeight b (4*T+3)) (hc : RationalHeight (op.apply a b) (4*T+3)) :
      price model (scalar op a b).2≤15*model.rat W := by
    have hf:=scalar_fits W op a b (hcommon a ha) (hcommon b hb) (hcommon _ hc) (by unfold W; omega)
    have hp:=price_bound model W (by unfold W; omega) _ hf
    simpa only [scalar_length] using hp
  have c1:=scalar_bound .add node.lo (M:ℚ) (hlo.mono (by omega)) (hMh.mono (by omega)) (hs.mono (by omega))
  have c2:=scalar_bound .multiply 2 (M:ℚ) (htwo.mono (by omega)) (hMh.mono (by omega)) (hspan.mono (by omega))
  have c3:=scalar_bound .divide shifted.1 span.1 (hs.mono (by omega)) (hspan.mono (by omega)) (hn.mono (by omega))
  have c4:=scalar_bound .multiply (C:ℚ) normalized.1 (hCh.mono (by omega)) (hn.mono (by omega)) hl
  have hnum : binaryWordWidth located.1.num.natAbs≤4*T+3 := binaryWordWidth_le_of_lt_pow (by omega) hl.1
  have hden : binaryWordWidth located.1.den≤4*T+3 := binaryWordWidth_le_of_lt_pow (by omega) hl.2
  have hnat : located.1.num.toNat≤located.1.num.natAbs := by omega
  have hnnum:=binaryWordWidth_mono hnat
  have hquot:=binaryWordWidth_mono (Nat.div_le_self located.1.num.toNat located.1.den)
  have hqo : binaryWordWidth quotient.1≤4*T+3 := hquot.trans (hnnum.trans hnum)
  have cq:=PlayerSpecificNaturalExecution.binary_cost model (fun a b => a/b) located.1.num.toNat located.1.den W
    (by unfold W; omega) (by unfold W; omega) (by unfold W; omega)
  have hmeta : 64*(5+binaryWordWidth M+binaryWordWidth C+binaryWordWidth located.1.num.natAbs+
      binaryWordWidth located.1.den+binaryWordWidth quotient.1)≤64*W := by unfold W; omega
  have hmetap:=hmeta.trans (Nat.mul_le_mul_left 64 (model.word_le W))
  change price model (shifted.2++span.2++normalized.2++located.2)+quotient.2+
    64*(5+binaryWordWidth M+binaryWordWidth C+binaryWordWidth located.1.num.natAbs+
      binaryWordWidth located.1.den+binaryWordWidth quotient.1)≤_
  simp only [price_append]
  change _≤5000*model.rat W
  nlinarith only [c1,c2,c3,c4,cq,hmetap]

end Blotto.PlayerSpecificReconstructionIndex
