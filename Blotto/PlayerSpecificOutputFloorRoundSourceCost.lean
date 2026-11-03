import Blotto.PlayerSpecificOutputFloorSearchSourceCost

/-! Source cost of one actual rational dyadic floor, including the
returned rational and four copied algebraic/rational rows. -/
namespace Blotto.PlayerSpecificOutputFloorRoundSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights
open PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (T P : ℕ) : ℕ :=
  let R:=RationalCostModel.schoolbook.rat
    (PlayerSpecificOutputFloorSearchSourceCost.width T P)
  PlayerSpecificOutputFloorSearchSourceCost.work T P+
    (256*(P+1)+278)*R

theorem index_bound (root : Candidate) (a : Data) (P : ℕ) :
    (PlayerSpecificOutputFloorExecution.search root a P).1.1≤2^P+1 := by
  let model:=RationalCostModel.schoolbook
  let cap:=PlayerSpecificNaturalExecution.power model 2 P
  let top:=PlayerSpecificNaturalExecution.binary model (fun x y=>x+y) cap.1 1
  have ht : top.1=2^P+1 := by
    simp only [top,cap,PlayerSpecificNaturalExecution.binary_value,
      PlayerSpecificNaturalExecution.power_value]
  have hr:=PlayerSpecificMeasuredCodeSearch.range model (binaryWordWidth top.1)
    (PlayerSpecificOutputFloorPredicateExecution.run root a P) 0 top.1 (by omega)
  change (PlayerSpecificMeasuredCodeSearch.run model (binaryWordWidth top.1)
    (PlayerSpecificOutputFloorPredicateExecution.run root a P) 0 top.1).1.1≤2^P+1
  exact hr.2.trans_eq ht

theorem rational_height (root : Candidate) (a : Data) (P : ℕ) :
    RationalHeight (PlayerSpecificOutputFloorExecution.round root a P).1 (P+3) := by
  let code:=(PlayerSpecificOutputFloorExecution.search root a P).1.1
  have hi : code≤2^P+1 := index_bound root a P
  have hn : (code:ℤ).natAbs<2^(P+3) := by
    simp only [Int.natAbs_natCast]
    rw [pow_add]
    norm_num only [Nat.reducePow]
    have hp : 1≤2^P := Nat.one_le_two_pow
    omega
  have hd : 2^P<2^(P+3) := by
    rw [pow_add]
    norm_num only [Nat.reducePow]
    have hp : 0<2^P := Nat.two_pow_pos P
    omega
  have hh:=RationalHeight.fraction (code:ℤ) (2^P) (P+3)
    (Nat.two_pow_pos P) hn hd
  simpa only [PlayerSpecificOutputFloorExecution.round,
    PlayerSpecificNaturalExecution.power_value,Int.cast_natCast,
    Nat.cast_pow,Nat.cast_ofNat,code] using hh

theorem cost (root : Candidate) (a : Data) (T P : ℕ)
    (hm : PlayerSpecificPolynomialNormalization.Normalized root.polynomial)
    (hm0 : root.polynomial≠[])
    (hml : root.polynomial.length≤4)
    (hv : root.interval.lo<root.interval.hi)
    (hroot : HasHeight root.polynomial T)
    (hends : HasHeight [root.interval.lo,root.interval.hi] T)
    (ha : PlayerSpecificAlgebraicReduction.Reduced root.polynomial a ∧ HasHeight a T) :
    (PlayerSpecificOutputFloorExecution.round root a P).2≤work T P := by
  let model:=RationalCostModel.schoolbook
  let search:=PlayerSpecificOutputFloorExecution.search root a P
  let denominator:=PlayerSpecificNaturalExecution.power model 2 P
  let value:ℚ:=(search.1.1:ℚ)/(denominator.1:ℚ)
  let divided:=GeneralPaperRationalPrimitivePrice.binary model.rat
    (fun u v=>u/v) (search.1.1:ℚ) (denominator.1:ℚ)
  let U:=PlayerSpecificOutputFloorPredicateSourceCost.height T P
  let W:=PlayerSpecificOutputFloorSearchSourceCost.width T P
  let R:=model.rat W
  have hsearch:=PlayerSpecificOutputFloorSearchSourceCost.cost root a T P
    hm hm0 hml hv hroot hends ha
  have hsmall : P+3≤U := by
    have hc:=PlayerSpecificAlgebraicHeightEnvelope.large
      (PlayerSpecificOutputFloorPredicateSourceCost.inputHeight T P)
    have hs : P+2≤PlayerSpecificOutputFloorPredicateSourceCost.inputHeight T P := by
      dsimp only [PlayerSpecificOutputFloorPredicateSourceCost.inputHeight]
      omega
    change PlayerSpecificOutputFloorPredicateSourceCost.inputHeight T P+1≤U at hc
    omega
  have hT : T≤U := by
    have hc:=PlayerSpecificAlgebraicHeightEnvelope.large
      (PlayerSpecificOutputFloorPredicateSourceCost.inputHeight T P)
    change PlayerSpecificOutputFloorPredicateSourceCost.inputHeight T P+1≤U at hc
    dsimp only [PlayerSpecificOutputFloorPredicateSourceCost.inputHeight] at hc
    omega
  have hWL:=PlayerSpecificAlgebraicActiveListCost.width_large U
  have hWL' : 32≤W ∧ 1+2*U≤W := by
    simpa only [W,PlayerSpecificOutputFloorSearchSourceCost.width,U,
      PlayerSpecificOutputFloorPredicateSourceCost.height] using
      ⟨hWL.1,hWL.2.1⟩
  have hpow : denominator.2≤256*(P+1)*R := by
    have hc:=PlayerSpecificAlgebraicHeightEnvelope.calibrate 64
      (PlayerSpecificOutputFloorPredicateSourceCost.inputHeight T P)
      (by unfold PlayerSpecificAlgebraicHeightEnvelope.coefficient; omega)
    have hs : P+2≤PlayerSpecificOutputFloorPredicateSourceCost.inputHeight T P := by
      dsimp only [PlayerSpecificOutputFloorPredicateSourceCost.inputHeight]
      omega
    change 64*(PlayerSpecificOutputFloorPredicateSourceCost.inputHeight T P+1)≤U at hc
    have h2 : binaryWordWidth 2=2 := by decide
    have hpowerWidth : PlayerSpecificNaturalExecution.powerWidth 2 P≤W := by
      dsimp [PlayerSpecificNaturalExecution.powerWidth]
      rw [h2]
      omega
    exact (PlayerSpecificNaturalExecution.power_cost model 2 P).trans
      (Nat.mul_le_mul_left _ (model.monotone hpowerWidth))
  have hindex : search.1.1≤2^P+1 := index_bound root a P
  have hcode : search.1.1≤2^(P+1) := by
    rw [pow_succ]
    have hp : 1≤2^P := Nat.one_le_two_pow
    omega
  have hnumHeight : RationalHeight (search.1.1:ℚ) (P+3) := by
    have hn : ((search.1.1:ℕ):ℤ).natAbs<2^(P+3) := by
      simp only [Int.natAbs_natCast]
      rw [pow_add]
      norm_num only [Nat.reducePow]
      have hp : 1≤2^P := Nat.one_le_two_pow
      omega
    have hone : 1<2^(P+3) := by
      have hp : 0<2^P := Nat.two_pow_pos P
      rw [pow_add]
      norm_num only [Nat.reducePow]
      omega
    simpa only [Int.cast_natCast,Nat.cast_one,div_one] using
      RationalHeight.fraction ((search.1.1:ℕ):ℤ) 1 (P+3) (by decide) hn hone
  have hdenHeight : RationalHeight (denominator.1:ℚ) (P+3) := by
    rw [PlayerSpecificNaturalExecution.power_value]
    have hn : ((2^P:ℕ):ℤ).natAbs<2^(P+3) := by
      simp only [Int.natAbs_natCast]
      rw [pow_add]
      norm_num only [Nat.reducePow]
      have hp : 0<2^P := Nat.two_pow_pos P
      omega
    have hone : 1<2^(P+3) := by
      rw [pow_add]
      norm_num only [Nat.reducePow]
      have hp : 0<2^P := Nat.two_pow_pos P
      omega
    simpa only [Int.cast_natCast,Nat.cast_one,div_one] using
      RationalHeight.fraction ((2^P:ℕ):ℤ) 1 (P+3) (by decide) hn hone
  have hvalue : RationalHeight value (P+3) := by
    simpa only [value,search,denominator,model,
      PlayerSpecificOutputFloorExecution.round] using rational_height root a P
  have hratWidth (q : ℚ) (hq : RationalHeight q (P+3)) : rationalWordWidth q≤W :=
    (rationalWordWidth_of_height hq).trans (by omega)
  have hdiv : divided≤2*R :=
    GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone
      (fun u v=>u/v) (search.1.1:ℚ) (denominator.1:ℚ) W
      (hratWidth _ hnumHeight) (hratWidth _ hdenHeight) (hratWidth _ hvalue)
  have hrow : ∀ row∈[root.polynomial,[root.interval.lo,root.interval.hi],a,[value]],
      HasHeight row U := by
    intro row hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with hr|hr|hr|hr
    · rw [hr]; exact PlayerSpecificPolynomialHeights.mono hroot hT
    · rw [hr]; exact PlayerSpecificPolynomialHeights.mono hends hT
    · rw [hr]; exact PlayerSpecificPolynomialHeights.mono ha.2 hT
    · rw [hr]; exact PlayerSpecificPolynomialHeights.cons_height
        (hvalue.mono hsmall) (PlayerSpecificPolynomialHeights.nil_height _)
  have hlen : ∀ row∈[root.polynomial,[root.interval.lo,root.interval.hi],a,[value]],
      row.length≤21 := by
    intro row hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with hr|hr|hr|hr
    · rw [hr]; omega
    · rw [hr]; simp
    · rw [hr]; have hl:=ha.1.2; omega
    · rw [hr]; simp
  have hwords : ∀ word∈[P,search.1.1,search.1.2,denominator.1],
      binaryWordWidth word≤W := by
    intro word hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with hw|hw|hw|hw
    · rw [hw]; exact (control_width P).trans (by omega)
    · rw [hw]; exact (PlayerSpecificOutputFloorSourceSizes.code_width (P+1)
        search.1.1 hcode).1.trans (by omega)
    · rw [hw]; exact (control_width search.1.2).trans
        (by
          have hv : search.1.2≤P+2 := PlayerSpecificOutputFloorExecution.visits root a P
          omega)
    · rw [hw,PlayerSpecificNaturalExecution.power_value,
        PlayerSpecificIsolationDepthHeight.two_power_width]
      omega
  have hframe:=PlayerSpecificAlgebraicCallerFrame.cost model
    [root.polynomial,[root.interval.lo,root.interval.hi],a,[value]]
    [P,search.1.1,search.1.2,denominator.1] U W
    hrow hlen hwords hWL'.2 hWL'.1
  have hframe' : price model (PlayerSpecificAlgebraicCallerFrame.run
      [root.polynomial,[root.interval.lo,root.interval.hi],a,[value]]
      [P,search.1.1,search.1.2,denominator.1])≤276*R := by
    norm_num at hframe
    exact hframe
  change search.2+denominator.2+divided+
    price model (PlayerSpecificAlgebraicCallerFrame.run
      [root.polynomial,[root.interval.lo,root.interval.hi],a,[value]]
      [P,search.1.1,search.1.2,denominator.1])≤_
  have hsum:=Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hsearch hpow) hdiv) hframe'
  have hshape : PlayerSpecificOutputFloorSearchSourceCost.work T P+
      256*(P+1)*R+2*R+276*R=work T P := by
    dsimp only [work,R,W]
    ring
  exact hsum.trans_eq hshape

end Blotto.PlayerSpecificOutputFloorRoundSourceCost
