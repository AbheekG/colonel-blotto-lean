import Blotto.PlayerSpecificMeasuredCodeSearchCost

/-! Source cost of the actual dyadic floor search, including cap
construction, its one-branch measured search, and the caller frame. -/
namespace Blotto.PlayerSpecificOutputFloorSearchSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights
open PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def width (T P : ℕ) : ℕ :=
  PlayerSpecificAlgebraicComparisonExecution.width
    (PlayerSpecificOutputFloorPredicateSourceCost.height T P)

def work (T P : ℕ) : ℕ :=
  let R:=RationalCostModel.schoolbook.rat (width T P)
  (P+2)*(PlayerSpecificOutputFloorPredicateSourceCost.work T P+150*R)+
    (256*(P+1)+157)*R

theorem cost (root : Candidate) (a : Data) (T P : ℕ)
    (hm : PlayerSpecificPolynomialNormalization.Normalized root.polynomial)
    (hm0 : root.polynomial≠[])
    (hml : root.polynomial.length≤4)
    (hv : root.interval.lo<root.interval.hi)
    (hroot : HasHeight root.polynomial T)
    (hends : HasHeight [root.interval.lo,root.interval.hi] T)
    (ha : PlayerSpecificAlgebraicReduction.Reduced root.polynomial a ∧ HasHeight a T) :
    (PlayerSpecificOutputFloorExecution.search root a P).2≤work T P := by
  let model:=RationalCostModel.schoolbook
  let C:=2^P
  let cap:=PlayerSpecificNaturalExecution.power model 2 P
  let top:=PlayerSpecificNaturalExecution.binary model (fun x y=>x+y) cap.1 1
  let F:=binaryWordWidth top.1
  let pred:=PlayerSpecificOutputFloorPredicateExecution.run root a P
  let found:=PlayerSpecificMeasuredCodeSearch.run model F pred 0 top.1
  let W:=width T P
  let R:=model.rat W
  let U:=PlayerSpecificOutputFloorPredicateSourceCost.height T P
  have hTU : T≤U := by
    have h:=PlayerSpecificAlgebraicHeightEnvelope.large
      (PlayerSpecificOutputFloorPredicateSourceCost.inputHeight T P)
    dsimp [U,PlayerSpecificOutputFloorPredicateSourceCost.height,
      PlayerSpecificOutputFloorPredicateSourceCost.inputHeight] at *
    omega
  have hPU : P+2≤U := by
    have h:=PlayerSpecificAlgebraicHeightEnvelope.large
      (PlayerSpecificOutputFloorPredicateSourceCost.inputHeight T P)
    dsimp [U,PlayerSpecificOutputFloorPredicateSourceCost.height,
      PlayerSpecificOutputFloorPredicateSourceCost.inputHeight] at *
    omega
  have hWL:=PlayerSpecificAlgebraicActiveListCost.width_large U
  have hWL' : 32≤W ∧ 1+2*U≤W ∧ U+1≤W := by
    simpa only [W,width,U,PlayerSpecificOutputFloorPredicateSourceCost.height] using hWL
  have hW : 32≤W := hWL'.1
  have hWPU : P+4≤W := by
    omega
  have hS : P+2≤PlayerSpecificOutputFloorPredicateSourceCost.inputHeight T P := by
    dsimp only [PlayerSpecificOutputFloorPredicateSourceCost.inputHeight]
    omega
  have h64 : 64*(P+3)≤U := by
    have hc:=PlayerSpecificAlgebraicHeightEnvelope.calibrate 64
      (PlayerSpecificOutputFloorPredicateSourceCost.inputHeight T P)
      (by unfold PlayerSpecificAlgebraicHeightEnvelope.coefficient; omega)
    change 64*(PlayerSpecificOutputFloorPredicateSourceCost.inputHeight T P+1)≤U at hc
    omega
  have hpow : cap.2≤256*(P+1)*R := by
    have h:=PlayerSpecificNaturalExecution.power_cost model 2 P
    have hsmall : PlayerSpecificNaturalExecution.powerWidth 2 P≤W := by
      have h2 : binaryWordWidth 2=2 := by decide
      dsimp [PlayerSpecificNaturalExecution.powerWidth]
      rw [h2]
      omega
    exact h.trans (Nat.mul_le_mul_left _ (model.monotone hsmall))
  have hCW:=PlayerSpecificOutputFloorSourceSizes.code_width P C (le_rfl)
  have htop : top.1=C+1 := by simp only [top,cap,PlayerSpecificNaturalExecution.binary_value,
    PlayerSpecificNaturalExecution.power_value,C]
  have hF : F≤P+2 := by dsimp only [F]; rw [htop]; exact hCW.2
  have hFC : F≤C+2 := by
    dsimp only [F]
    exact (control_width top.1).trans (by rw [htop])
  have htopCost : top.2≤64*R := by
    apply PlayerSpecificNaturalExecution.binary_cost model (fun x y=>x+y) cap.1 1 W
    · rw [PlayerSpecificNaturalExecution.power_value]
      rw [PlayerSpecificIsolationDepthHeight.two_power_width]
      omega
    · have h1 : binaryWordWidth 1=1 := by decide
      rw [h1]
      omega
    · rw [PlayerSpecificNaturalExecution.power_value]
      exact Nat.add_le_add_left hCW.2 1 |>.trans (by omega)
  have hpred : ∀ code≤C,(pred code).2≤PlayerSpecificOutputFloorPredicateSourceCost.work T P := by
    intro code hc
    exact PlayerSpecificOutputFloorPredicateSourceCost.cost root a T P code
      hm hm0 hml hv hroot hends ha hc
  have hsearch:=PlayerSpecificMeasuredCodeSearchCost.cost model C
    (PlayerSpecificOutputFloorPredicateSourceCost.work T P) F pred 0 top.1
    (by omega) (by rw [htop]) hFC hpred
  have hSW : PlayerSpecificMeasuredCodeSearchCost.width C≤W := by
    have hc2 : C+2≤2^(P+2) := by
      dsimp only [C]
      rw [pow_add]
      norm_num only [Nat.reducePow]
      have ht : 1≤2^P := Nat.one_le_two_pow
      omega
    have hb:=binaryWordWidth_mono hc2
    rw [PlayerSpecificIsolationDepthHeight.two_power_width] at hb
    dsimp only [PlayerSpecificMeasuredCodeSearchCost.width]
    omega
  have hsearch' : found.2≤(P+2)*(PlayerSpecificOutputFloorPredicateSourceCost.work T P+150*R)+9*R := by
    have hmrat:=model.monotone hSW
    have hwork : PlayerSpecificMeasuredCodeSearchCost.work model C F
        (PlayerSpecificOutputFloorPredicateSourceCost.work T P)≤
        (P+2)*(PlayerSpecificOutputFloorPredicateSourceCost.work T P+150*R)+9*R := by
      unfold PlayerSpecificMeasuredCodeSearchCost.work
      have hA : PlayerSpecificOutputFloorPredicateSourceCost.work T P+
          150*model.rat (PlayerSpecificMeasuredCodeSearchCost.width C)≤
          PlayerSpecificOutputFloorPredicateSourceCost.work T P+150*R :=
        Nat.add_le_add_left (Nat.mul_le_mul_left 150 hmrat) _
      have hmul:=Nat.mul_le_mul_left F hA
      have hmul2:=Nat.mul_le_mul_right
        (PlayerSpecificOutputFloorPredicateSourceCost.work T P+150*R) hF
      exact Nat.add_le_add
        (hmul.trans hmul2)
        (Nat.mul_le_mul_left 9 hmrat)
    exact hsearch.trans hwork
  have hfoundCode : found.1.1≤C+1 := by
    have hr:=PlayerSpecificMeasuredCodeSearch.range model F pred 0 top.1 (by omega)
    simpa only [found,htop] using hr.2
  have hfoundVisits : found.1.2≤F := PlayerSpecificMeasuredCodeSearch.visits model F pred 0 top.1
  have wordBound (n : ℕ) (hn : n≤C+2) : binaryWordWidth n≤W := by
    have hb:=binaryWordWidth_mono hn
    have hs:=hSW
    dsimp only [PlayerSpecificMeasuredCodeSearchCost.width] at hs
    omega
  have hwords : ∀ word∈[P,cap.1,top.1,F,found.1.1,found.1.2],
      binaryWordWidth word≤W := by
    intro word hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with hw|hw|hw|hw|hw|hw
    · simpa only [hw] using (control_width P).trans (by omega : P+1≤W)
    · rw [hw,PlayerSpecificNaturalExecution.power_value]
      exact wordBound C (by omega)
    · simpa only [hw,htop] using wordBound (C+1) (by omega)
    · simpa only [hw] using (control_width F).trans (by omega : F+1≤W)
    · simpa only [hw] using wordBound found.1.1 (by omega)
    · simpa only [hw] using (control_width found.1.2).trans (by omega : found.1.2+1≤W)
  have hrow : ∀ row∈[a],HasHeight row U := by
    intro row hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rw [hr]
    exact PlayerSpecificPolynomialHeights.mono ha.2 hTU
  have hlen : ∀ row∈[a],row.length≤21 := by
    intro row hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rw [hr]
    have hl:=ha.1.2
    omega
  have hframe:=PlayerSpecificAlgebraicCallerFrame.cost model [a]
    [P,cap.1,top.1,F,found.1.1,found.1.2] U W hrow hlen hwords
    (by dsimp only [W,width]; exact hWL.2.1)
    hW
  have hframe' : price model (PlayerSpecificAlgebraicCallerFrame.run [a]
      [P,cap.1,top.1,F,found.1.1,found.1.2])≤84*R := by
    norm_num at hframe
    exact hframe
  change cap.2+top.2+found.2+price model (PlayerSpecificAlgebraicCallerFrame.run [a]
    [P,cap.1,top.1,F,found.1.1,found.1.2])≤_
  have hsum:=Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hpow htopCost) hsearch') hframe'
  have hshape : 256*(P+1)*R+64*R+
      ((P+2)*(PlayerSpecificOutputFloorPredicateSourceCost.work T P+150*R)+9*R)+84*R
      = work T P := by dsimp only [work,R,W]; ring
  exact hsum.trans_eq hshape

end Blotto.PlayerSpecificOutputFloorSearchSourceCost
