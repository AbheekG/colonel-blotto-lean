import Blotto.PlayerSpecificRationalPrecisionSourceSizes
import Blotto.PlayerSpecificAlgebraicCallerFrame

/-! Schoolbook source bound for the complete executing scaled-precision
selector, including its two halving-based word lengths, dyadic power,
comparison, and all copied words. -/
namespace Blotto.PlayerSpecificRationalPrecisionSourceCost
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (C : ℕ) (epsilon : ℚ) : ℕ :=
  let L:=PlayerSpecificRationalPrecisionSourceSizes.inputWidth C epsilon
  let W:=PlayerSpecificRationalPrecisionSourceSizes.width C epsilon
  1000*(L+1)*RationalCostModel.schoolbook.rat W

theorem cost (C : ℕ) (epsilon : ℚ) :
    (PlayerSpecificRationalPrecisionExecution.run C epsilon).2≤work C epsilon := by
  let model:=RationalCostModel.schoolbook
  let L:=PlayerSpecificRationalPrecisionSourceSizes.inputWidth C epsilon
  let W:=PlayerSpecificRationalPrecisionSourceSizes.width C epsilon
  let R:=model.rat W
  let a:=PlayerSpecificNaturalExecution.binary model (fun x y=>x*y) C epsilon.den
  let b:=epsilon.num.toNat
  let wa:=PlayerSpecificWidthExecution.run model a.1
  let wb:=PlayerSpecificWidthExecution.run model b
  let candidate:=PlayerSpecificNaturalExecution.binary model (fun x y=>x-y) wa.1 wb.1
  let power:=PlayerSpecificNaturalExecution.power model 2 candidate.1
  let scaled:=PlayerSpecificNaturalExecution.binary model (fun x y=>x*y) b power.1
  let increased:=PlayerSpecificNaturalExecution.binary model (fun x y=>x+y) candidate.1 1
  let tested:=GeneralPaperIntegerWordPrice.compare model.rat a.1 scaled.1
  let words:List ℕ:=[C,epsilon.den,b,a.1,wa.1,wb.1,candidate.1,power.1,
    scaled.1,increased.1]
  have hW : 1≤W := by dsimp [W,PlayerSpecificRationalPrecisionSourceSizes.width]; omega
  have hL : L+1≤W := by dsimp [W,PlayerSpecificRationalPrecisionSourceSizes.width]; omega
  have hLW : 2*L+3≤W := by dsimp [W,PlayerSpecificRationalPrecisionSourceSizes.width]; omega
  have hC : binaryWordWidth C≤L := by dsimp only [L,PlayerSpecificRationalPrecisionSourceSizes.inputWidth]; omega
  have hden : binaryWordWidth epsilon.den≤L := by
    dsimp only [L,PlayerSpecificRationalPrecisionSourceSizes.inputWidth,rationalWordWidth]
    omega
  have hb : binaryWordWidth b≤L := PlayerSpecificRationalPrecisionSourceSizes.denominator_width C epsilon
  have ha : binaryWordWidth a.1≤L := by
    rw [PlayerSpecificNaturalExecution.binary_value]
    exact PlayerSpecificRationalPrecisionSourceSizes.numerator_width C epsilon
  have hwa : wa.1≤L := by rw [PlayerSpecificWidthExecution.value]; exact ha
  have hwb : wb.1≤L := by rw [PlayerSpecificWidthExecution.value]; exact hb
  have hcand : candidate.1≤L := by rw [PlayerSpecificNaturalExecution.binary_value]; omega
  have hpower : binaryWordWidth power.1≤L+1 := by
    rw [PlayerSpecificNaturalExecution.power_value,
      PlayerSpecificNaturalExecution.binary_value,
      PlayerSpecificWidthExecution.value,PlayerSpecificWidthExecution.value,
      PlayerSpecificNaturalExecution.binary_value]
    exact PlayerSpecificRationalPrecisionSourceSizes.power_width C epsilon
  have hscaled : binaryWordWidth scaled.1≤2*L+1 := by
    rw [PlayerSpecificNaturalExecution.binary_value,
      PlayerSpecificNaturalExecution.power_value,
      PlayerSpecificNaturalExecution.binary_value,
      PlayerSpecificWidthExecution.value,PlayerSpecificWidthExecution.value,
      PlayerSpecificNaturalExecution.binary_value]
    exact PlayerSpecificRationalPrecisionSourceSizes.scaled_width C epsilon
  have hinc : increased.1≤L+1 := by
    rw [PlayerSpecificNaturalExecution.binary_value]
    omega
  have hword (n : ℕ) (hn : n≤L+1) : 1+binaryWordWidth n≤W := by
    have hw:=control_width n
    omega
  have hword' (n : ℕ) (hn : binaryWordWidth n≤2*L+1) :
      1+binaryWordWidth n≤W := by omega
  have haCost:=PlayerSpecificNaturalExecution.binary_cost model (fun x y=>x*y)
    C epsilon.den W (hword' C (by omega)) (hword' epsilon.den (by omega))
    (hword' a.1 (by omega))
  have hwaCost : wa.2≤128*(L+1)*R := by
    have h:=PlayerSpecificWidthExecution.price model a.1
    have hwidth : PlayerSpecificWidthExecution.width a.1≤W := by
      dsimp only [PlayerSpecificWidthExecution.width,W,
        PlayerSpecificRationalPrecisionSourceSizes.width]
      omega
    have hr:=model.monotone hwidth
    have hstep:=Nat.mul_le_mul_left (128*(binaryWordWidth a.1+1)) hr
    have hcount:=Nat.mul_le_mul_right R (Nat.mul_le_mul_left 128 (by omega : binaryWordWidth a.1+1≤L+1))
    exact h.trans (hstep.trans hcount)
  have hwbCost : wb.2≤128*(L+1)*R := by
    have h:=PlayerSpecificWidthExecution.price model b
    have hwidth : PlayerSpecificWidthExecution.width b≤W := by
      dsimp only [PlayerSpecificWidthExecution.width,W,
        PlayerSpecificRationalPrecisionSourceSizes.width]
      omega
    have hr:=model.monotone hwidth
    have hstep:=Nat.mul_le_mul_left (128*(binaryWordWidth b+1)) hr
    have hcount:=Nat.mul_le_mul_right R (Nat.mul_le_mul_left 128 (by omega : binaryWordWidth b+1≤L+1))
    exact h.trans (hstep.trans hcount)
  have hcandCost:=PlayerSpecificNaturalExecution.binary_cost model (fun x y=>x-y)
    wa.1 wb.1 W (hword wa.1 (by omega)) (hword wb.1 (by omega))
    (hword _ (by omega))
  have hpowCost : power.2≤256*(L+1)*R := by
    have h:=PlayerSpecificNaturalExecution.power_cost model 2 candidate.1
    have hwidth : PlayerSpecificNaturalExecution.powerWidth 2 candidate.1≤W := by
      have h2 : binaryWordWidth 2=2 := by decide
      dsimp only [PlayerSpecificNaturalExecution.powerWidth]
      rw [h2]
      dsimp only [W,PlayerSpecificRationalPrecisionSourceSizes.width]
      omega
    have hr:=model.monotone hwidth
    have hstep:=Nat.mul_le_mul_left (256*(candidate.1+1)) hr
    have hcount:=Nat.mul_le_mul_right R (Nat.mul_le_mul_left 256 (by omega : candidate.1+1≤L+1))
    exact h.trans (hstep.trans hcount)
  have hscaledCost:=PlayerSpecificNaturalExecution.binary_cost model (fun x y=>x*y)
    b power.1 W (hword' b (by omega)) (hword' power.1 (by omega))
    (hword' scaled.1 (by omega))
  have hincCost:=PlayerSpecificNaturalExecution.binary_cost model (fun x y=>x+y)
    candidate.1 1 W (hword candidate.1 (by omega))
    (hword 1 (by omega)) (hword increased.1 (by omega))
  have htest : tested≤R := GeneralPaperIntegerWordPrice.compare_le model.rat
    model.monotone a.1 scaled.1 W (hword' a.1 (by omega))
      (hword' scaled.1 (by omega))
  have hwords : ∀ word∈words,binaryWordWidth word≤W := by
    intro word hw
    simp only [words,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with hw|hw|hw|hw|hw|hw|hw|hw|hw|hw
    · rw [hw]; omega
    · rw [hw]; omega
    · rw [hw]; omega
    · rw [hw]; omega
    · rw [hw]; exact (control_width wa.1).trans (by omega)
    · rw [hw]; exact (control_width wb.1).trans (by omega)
    · rw [hw]; exact (control_width candidate.1).trans (by omega)
    · rw [hw]; omega
    · rw [hw]; omega
    · rw [hw]; exact (control_width increased.1).trans (by omega)
  have hctrl:=PlayerSpecificAlgebraicCallerFrame.controls_cost model words W hwords hW
  have hctrl' : price model (words.map Event.control)≤30*R := by
    have hl : words.length=10 := rfl
    rw [hl] at hctrl
    norm_num at hctrl
    exact hctrl
  have hcopyFits : Fits W (copyRow [epsilon]) := by
    intro e he
    simp only [copyRow,List.map_cons,List.map_nil,List.mem_cons,
      List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl
    · exact (control_width 1).trans (by omega)
    · dsimp only [Event.Fits]
      dsimp only [W,PlayerSpecificRationalPrecisionSourceSizes.width,
        PlayerSpecificRationalPrecisionSourceSizes.inputWidth]
      omega
  have hcopy:=price_bound model W hW (copyRow [epsilon]) hcopyFits
  have hcopy' : price model (copyRow [epsilon])≤6*R := by
    simpa only [copyRow,List.length_cons,List.length_map,List.length_nil,
      Nat.reduceAdd,Nat.reduceMul] using hcopy
  have hframe : price model (PlayerSpecificRationalPrecisionExecution.frame C epsilon
      a.1 b wa.1 wb.1 candidate.1 power.1 scaled.1 increased.1)≤36*R := by
    change price model (copyRow [epsilon]++words.map Event.control)≤_
    rw [price_append]
    omega
  change a.2+wa.2+wb.2+candidate.2+power.2+scaled.2+increased.2+tested+
    price model (PlayerSpecificRationalPrecisionExecution.frame C epsilon
      a.1 b wa.1 wb.1 candidate.1 power.1 scaled.1 increased.1)≤_
  have hsum:=Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add
              (Nat.add_le_add
                (Nat.add_le_add haCost hwaCost) hwbCost) hcandCost) hpowCost)
            hscaledCost) hincCost) htest) hframe
  have hshape : 64*R+128*(L+1)*R+128*(L+1)*R+64*R+
      256*(L+1)*R+64*R+64*R+R+36*R≤work C epsilon := by
    dsimp only [work,L,W]
    have hnonneg : 0≤L := Nat.zero_le L
    nlinarith
  exact hsum.trans hshape

end Blotto.PlayerSpecificRationalPrecisionSourceCost
