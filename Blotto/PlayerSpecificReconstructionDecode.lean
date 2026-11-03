import Blotto.PlayerSpecificReconstructionIndex

/-! Actual Farey decoding into original signed root coordinates, with
integer/rational casts, four rational operations and returned data priced. -/
namespace Blotto.PlayerSpecificReconstructionDecode
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 200000

def run (model : RationalCostModel) (M : ℕ) (f : Farey.Fraction) : ℚ×ℕ :=
  let fraction:=scalar .divide (f.num:ℚ) (f.den:ℚ)
  let span:=scalar .multiply 2 (M:ℚ)
  let scaled:=scalar .multiply span.1 fraction.1
  let decoded:=scalar .subtract scaled.1 (M:ℚ)
  (decoded.1,price model (fraction.2++span.2++scaled.2++decoded.2++[.copy decoded.1,.control 1])+
    64*(4+binaryWordWidth M+binaryWordWidth f.num+binaryWordWidth f.den))

theorem value (model : RationalCostModel) (M : ℕ) (f : Farey.Fraction) :
    (run model M f).1=PlayerSpecificRationalReconstruction.decode M f := by
  simp only [run,scalar,Arithmetic.apply,PlayerSpecificRationalReconstruction.decode,Farey.Fraction.value]

theorem height (model : RationalCostModel) (M : ℕ) (f : Farey.Fraction) (T : ℕ)
    (hT : 2≤T) (hM : binaryWordWidth M≤T) (hn : binaryWordWidth f.num≤T) (hd : binaryWordWidth f.den≤T) :
    RationalHeight (run model M f).1 (4*T+3) := by
  have hm:=PlayerSpecificReconstructionIndex.natural_height M T (by omega) hM
  have hnum:=PlayerSpecificReconstructionIndex.natural_height f.num T (by omega) hn
  have hden:=PlayerSpecificReconstructionIndex.natural_height f.den T (by omega) hd
  have htwo : RationalHeight (2:ℚ) 2 := by norm_num [RationalHeight]
  have hfrac:=hnum.div hden
  have hspan:=htwo.mul hm
  have hscaled:=hspan.mul hfrac
  have hdecoded:=hscaled.sub hm
  simpa only [run,scalar,Arithmetic.apply,show (2+T+(T+T))+T+1=4*T+3 by omega] using hdecoded

theorem metadata_bound (T a b c : ℕ) (ha : a≤T) (hb : b≤T) (hc : c≤T) :
    64*(4+a+b+c)≤64*(32*(T+1)) := by omega

theorem run_cost (model : RationalCostModel) (M : ℕ) (f : Farey.Fraction) (T : ℕ)
    (hT : 2≤T) (hM : binaryWordWidth M≤T) (hn : binaryWordWidth f.num≤T) (hd : binaryWordWidth f.den≤T) :
    (run model M f).2≤5000*model.rat (32*(T+1)) := by
  let W:=32*(T+1)
  let fraction:=scalar .divide (f.num:ℚ) (f.den:ℚ)
  let span:=scalar .multiply 2 (M:ℚ)
  let scaled:=scalar .multiply span.1 fraction.1
  let decoded:=scalar .subtract scaled.1 (M:ℚ)
  have hm:=PlayerSpecificReconstructionIndex.natural_height M T (by omega) hM
  have hnum:=PlayerSpecificReconstructionIndex.natural_height f.num T (by omega) hn
  have hden:=PlayerSpecificReconstructionIndex.natural_height f.den T (by omega) hd
  have htwo : RationalHeight (2:ℚ) 2 := by norm_num [RationalHeight]
  have hfrac : RationalHeight fraction.1 (2*T) := by simpa only [fraction,scalar,Arithmetic.apply,two_mul] using hnum.div hden
  have hspan : RationalHeight span.1 (T+2) := by simpa only [span,scalar,Arithmetic.apply,Nat.add_comm] using htwo.mul hm
  have hscaled : RationalHeight scaled.1 (3*T+2) := by
    simpa only [scaled,scalar,Arithmetic.apply,show (T+2)+2*T=3*T+2 by omega] using hspan.mul hfrac
  have hdecoded : RationalHeight decoded.1 (4*T+3) := height model M f T hT hM hn hd
  have fits (q : ℚ) (hq : RationalHeight q (4*T+3)) : rationalWordWidth q≤W :=
    (rationalWordWidth_of_height hq).trans (by unfold W; omega)
  have step (op : Arithmetic) (a b : ℚ) (ha : RationalHeight a (4*T+3))
      (hb : RationalHeight b (4*T+3)) (hc : RationalHeight (op.apply a b) (4*T+3)) :
      price model (scalar op a b).2≤15*model.rat W := by
    have hp:=price_bound model W (by unfold W; omega) _ (scalar_fits W op a b (fits a ha) (fits b hb) (fits _ hc) (by unfold W; omega))
    simpa only [scalar_length] using hp
  have c1:=step .divide (f.num:ℚ) (f.den:ℚ) (hnum.mono (by omega)) (hden.mono (by omega)) (hfrac.mono (by omega))
  have c2:=step .multiply 2 (M:ℚ) (htwo.mono (by omega)) (hm.mono (by omega)) (hspan.mono (by omega))
  have c3:=step .multiply span.1 fraction.1 (hspan.mono (by omega)) (hfrac.mono (by omega)) (hscaled.mono (by omega))
  have c4:=step .subtract scaled.1 (M:ℚ) (hscaled.mono (by omega)) (hm.mono (by omega)) hdecoded
  have htail : Fits W [.copy decoded.1,.control 1] := by
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl
    · exact fits _ hdecoded
    · exact (control_width 1).trans (by unfold W; omega)
  have ctail:=price_bound model W (by unfold W; omega) _ htail
  simp only [List.length_cons,List.length_nil] at ctail
  have hmeta : 64*(4+binaryWordWidth M+binaryWordWidth f.num+binaryWordWidth f.den)≤64*W :=
    metadata_bound T _ _ _ hM hn hd
  have hmetap:=hmeta.trans (Nat.mul_le_mul_left 64 (model.word_le W))
  rw [run]
  dsimp only
  simp only [price_append]
  nlinarith only [c1,c2,c3,c4,ctail,hmetap]

end Blotto.PlayerSpecificReconstructionDecode
