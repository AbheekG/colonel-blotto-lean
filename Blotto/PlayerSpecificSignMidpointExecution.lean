import Blotto.PlayerSpecificRationalSignExecution

/-! Actual midpoint arithmetic, exact rational Horner and total sign test,
including complete input, endpoint and returned scalar/control copies. -/
namespace Blotto.PlayerSpecificSignMidpointExecution
open SignType PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificIsolationState PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2000000

def run (a : Data) (node : Interval) : SignType×Trace :=
  let added:=scalar .add node.lo node.hi
  let middle:=scalar .divide added.1 2
  let evaluated:=PlayerSpecificDenseExecution.evaluate a middle.1
  let signed:=PlayerSpecificRationalSignExecution.run evaluated.1
  (signed.1,copyRow a++copyRow [node.lo,node.hi]++added.2++middle.2++evaluated.2++signed.2++[.copy middle.1,.copy evaluated.1,.control 1])

theorem value (a : Data) (node : Interval) : (run a node).1=sign (evaluate a node.midpoint) := by
  simp only [run,PlayerSpecificRationalSignExecution.value,PlayerSpecificDenseExecution.evaluate_value,
    scalar,Arithmetic.apply,Interval.midpoint]

theorem run_cost (model : RationalCostModel) (a : Data) (node : Interval) (H W : ℕ)
    (ha : HasHeight a H) (hal : a.length≤3) (hlo : RationalHeight node.lo H) (hhi : RationalHeight node.hi H)
    (hW : 1000*(H+1)≤W) : price model (run a node).2≤1000*model.rat W := by
  have h2 : RationalHeight (2:ℚ) 2 := by norm_num [RationalHeight]
  have hs : RationalHeight (scalar .add node.lo node.hi).1 (2*H+1) := by
    simpa only [scalar,Arithmetic.apply,two_mul] using hlo.add hhi
  have hm : RationalHeight (scalar .divide (scalar .add node.lo node.hi).1 2).1 (2*H+3) := by
    simpa only [scalar,Arithmetic.apply,Nat.add_assoc] using hs.div h2
  have hadd:=price_bound model W (by omega) _ (fits_mono (scalar_fits_height .add node.lo node.hi H hlo hhi) (by omega))
  have hmid:=price_bound model W (by omega) _ (fits_mono (scalar_fits_height .divide
    (scalar .add node.lo node.hi).1 2 (2*H+3) (hs.mono (by omega)) (h2.mono (by omega))) (by omega))
  rw [scalar_length] at hadd hmid
  have hev:=PlayerSpecificHornerTraceCost.evaluate_cost model a
    (scalar .divide (scalar .add node.lo node.hi).1 2).1 (2*H+3) 3 (mono ha (by omega)) hm hal
  have hew : PlayerSpecificHornerTraceCost.width (2*H+3) 3≤W := by
    unfold PlayerSpecificHornerTraceCost.width PlayerSpecificHornerTraceCost.valueHeight
    omega
  have hlen : 33*a.length+9≤108 := by omega
  have hevp:=hev.trans (Nat.mul_le_mul hlen (model.monotone hew))
  have heheight:=evaluate_height ha hm
  have hecap : (H+(2*H+3)+1)*a.length+1≤12*H+16 := by
    have hmul:=Nat.mul_le_mul_left (H+(2*H+3)+1) hal
    omega
  have heH : RationalHeight (PlayerSpecificDenseExecution.evaluate a
      (scalar .divide (scalar .add node.lo node.hi).1 2).1).1 (12*H+16) := by
    rw [PlayerSpecificDenseExecution.evaluate_value]
    exact heheight.mono hecap
  have hsign:=PlayerSpecificRationalSignExecution.run_cost model _ (12*H+16) W heH (by omega) (by omega) (by omega)
  have hap:=PlayerSpecificExtendedCopyCost.row_cost model a H W ha (by omega) (by omega) (by omega)
  have hep:=PlayerSpecificExtendedCopyCost.row_cost model [node.lo,node.hi] H W
    (cons_height hlo (cons_height hhi (nil_height H))) (by simp) (by omega) (by omega)
  have hfit : Fits W [.copy (scalar .divide (scalar .add node.lo node.hi).1 2).1,
      .copy (PlayerSpecificDenseExecution.evaluate a (scalar .divide (scalar .add node.lo node.hi).1 2).1).1,.control 1] := by
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl
    · exact (rationalWordWidth_of_height hm).trans (by omega)
    · exact (rationalWordWidth_of_height heH).trans (by omega)
    · exact (PlayerSpecificRationalTrace.control_width 1).trans (by omega)
  have hc:=price_bound model W (by omega) _ hfit
  simp only [List.length_cons,List.length_nil] at hc
  simp only [run,price_append]
  nlinarith only [hadd,hmid,hevp,hsign,hap,hep,hc]

end Blotto.PlayerSpecificSignMidpointExecution
