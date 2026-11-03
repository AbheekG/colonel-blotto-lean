import Blotto.PlayerSpecificOutputFloorSourceSizes

/-! An actually reached floor predicate costs polynomially in the input
algebraic row height and output precision. The code bound comes from the
search bracket; threshold arithmetic, constant construction, comparison,
copies and controls are all included. -/
namespace Blotto.PlayerSpecificOutputFloorPredicateSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope
open PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def inputHeight (T P : ℕ) : ℕ := max T (P+2)+2
def height (T P : ℕ) : ℕ := step (inputHeight T P)
def work (T P : ℕ) : ℕ :=
  (256*(P+1)+8000000408+PlayerSpecificAlgebraicComparisonExecution.coefficient*(height T P+1))*
    RationalCostModel.schoolbook.rat (PlayerSpecificAlgebraicComparisonExecution.width (height T P))

theorem cost (root : Candidate) (a : Data) (T P code : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hml : root.polynomial.length≤4)
    (hv : root.interval.lo<root.interval.hi)
    (hroot : HasHeight root.polynomial T)
    (hends : HasHeight [root.interval.lo,root.interval.hi] T)
    (ha : Reduced root.polynomial a ∧ HasHeight a T)
    (hcode : code≤2^P) :
    (PlayerSpecificOutputFloorPredicateExecution.run root a P code).2≤work T P := by
  let model:=RationalCostModel.schoolbook
  let S:=inputHeight T P
  let U:=height T P
  let W:=PlayerSpecificAlgebraicComparisonExecution.width U
  let power:=PlayerSpecificNaturalExecution.power model 2 P
  let numerator:=PlayerSpecificNaturalExecution.binary model (fun x y=>x+y) code 1
  let threshold:ℚ:=(numerator.1:ℚ)/(power.1:ℚ)
  let constant:=PlayerSpecificFieldCombinationContract.constant root.polynomial threshold
  let compared:=PlayerSpecificAlgebraicComparisonExecution.run model root constant.1 a
  let words:List ℕ:=[P,code,power.1,numerator.1]
  let rows:List Data:=[root.polynomial,[root.interval.lo,root.interval.hi],a,constant.1,[threshold]]
  have hTS : T≤S := by dsimp [S,inputHeight]; omega
  have hPS : P+2≤S := by dsimp [S,inputHeight]; omega
  have hSU : S≤U := (Nat.le_succ _).trans (large S)
  have hU : 1≤U := by omega
  have hWL := PlayerSpecificAlgebraicActiveListCost.width_large U
  have hW : 1≤W := by dsimp only [W]; omega
  have hq0 := PlayerSpecificOutputFloorSourceSizes.threshold_height P code hcode
  have hq : RationalHeight threshold S := by
    dsimp only [threshold]
    rw [PlayerSpecificNaturalExecution.binary_value,PlayerSpecificNaturalExecution.power_value]
    simpa only [PlayerSpecificAlgebraicOutputFloor.threshold,Nat.cast_pow,Nat.cast_ofNat] using
      hq0.mono hPS
  have hnumden := PlayerSpecificOutputFloorSourceSizes.operands_height P code hcode
  have hqWidth : rationalWordWidth threshold≤W :=
    (rationalWordWidth_of_height hq).trans (by dsimp only [W]; omega)
  have hnumWidth : rationalWordWidth (numerator.1:ℚ)≤W := by
    rw [PlayerSpecificNaturalExecution.binary_value]
    exact (rationalWordWidth_of_height hnumden.1).trans (by dsimp only [W]; omega)
  have hdenWidth : rationalWordWidth (power.1:ℚ)≤W := by
    rw [PlayerSpecificNaturalExecution.power_value]
    exact (rationalWordWidth_of_height hnumden.2).trans (by dsimp only [W]; omega)
  have hthreshold:=GeneralPaperRationalPrimitivePrice.binary_le model.rat model.monotone
    (fun u v=>u/v) (numerator.1:ℚ) (power.1:ℚ) W hnumWidth hdenWidth hqWidth
  have hStep64 : 64*(S+1)≤U := calibrate 64 S
    (by unfold PlayerSpecificAlgebraicHeightEnvelope.coefficient; omega)
  have hpowWidth : PlayerSpecificNaturalExecution.powerWidth 2 P≤W := by
    have h2 : binaryWordWidth 2=2 := by decide
    dsimp [PlayerSpecificNaturalExecution.powerWidth]
    rw [h2]
    dsimp only [W]
    omega
  have hpower:=PlayerSpecificNaturalExecution.power_cost model 2 P
  have hpower' : power.2≤256*(P+1)*model.rat W :=
    hpower.trans (Nat.mul_le_mul_left _ (model.monotone hpowWidth))
  have hcodeW := PlayerSpecificOutputFloorSourceSizes.code_width P code hcode
  have hcodeWord : 1+binaryWordWidth code≤W := by dsimp only [W]; omega
  have honeWord : 1+binaryWordWidth 1≤W := by
    have h1 : binaryWordWidth 1=1 := by decide
    rw [h1]
    dsimp only [W]
    omega
  have hsumWord : 1+binaryWordWidth (code+1)≤W := by dsimp only [W]; omega
  have hn := PlayerSpecificNaturalExecution.binary_cost model (fun x y=>x+y) code 1 W
    hcodeWord honeWord hsumWord
  have hconst:=PlayerSpecificAlgebraicExpressionPrimitiveCost.constant_cost model root threshold S
    hm hm0 hml (mono hroot hTS) hq (by omega)
  have hconst' : price model constant.2≤8000000000*model.rat W :=
    hconst.trans (Nat.mul_le_mul_left _ (model.monotone
      (PlayerSpecificSegmentSelectionSizes.width_mono hSU)))
  have hconstant : Reduced root.polynomial constant.1 ∧ HasHeight constant.1 U := by
    rw [PlayerSpecificFieldCombinationContract.constant_value]
    exact ⟨PlayerSpecificAlgebraicField.constant_reduced _ _ hm hm0,
      constant_height root.polynomial threshold S (mono hroot hTS) hq (by omega) hml⟩
  have hcmp := PlayerSpecificAlgebraicComparisonExecution.cost model root constant.1 a U
    hm hm0 hml (mono hroot (hTS.trans hSU)) (mono hends (hTS.trans hSU)) hv
    hconstant.2 (mono ha.2 (hTS.trans hSU))
    (by have h:=hconstant.1.2; omega) (by have h:=ha.1.2; omega) hU
  have hh : ∀ row∈rows,HasHeight row U := by
    intro row hr
    simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with hr|hr|hr|hr|hr
    · rw [hr]; exact mono hroot (hTS.trans hSU)
    · rw [hr]; exact mono hends (hTS.trans hSU)
    · rw [hr]; exact mono ha.2 (hTS.trans hSU)
    · rw [hr]; exact hconstant.2
    · rw [hr]; exact cons_height (hq.mono hSU) (nil_height _)
  have hl : ∀ row∈rows,row.length≤21 := by
    intro row hr
    simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with hr|hr|hr|hr|hr
    · rw [hr]; omega
    · rw [hr]; simp
    · rw [hr]; have h:=ha.1.2; omega
    · rw [hr]; have h:=hconstant.1.2; omega
    · rw [hr]; simp
  have hw : ∀ word∈words,binaryWordWidth word≤W := by
    intro word hword
    simp only [words,List.mem_cons,List.not_mem_nil,or_false] at hword
    rcases hword with hw|hw|hw|hw
    · rw [hw]; exact (control_width P).trans (by dsimp only [W]; omega)
    · rw [hw]; omega
    · rw [hw,PlayerSpecificNaturalExecution.power_value,
        PlayerSpecificIsolationDepthHeight.two_power_width]
      dsimp only [W]; omega
    · rw [hw,PlayerSpecificNaturalExecution.binary_value]
      omega
  have hframe:=PlayerSpecificAlgebraicCallerFrame.cost model rows words U W hh hl hw
    (by dsimp only [W]; exact hWL.2.1) (by dsimp only [W]; exact hWL.1)
  have hframe' : price model (PlayerSpecificOutputFloorPredicateExecution.frame root a constant.1 threshold P code power.1 numerator.1)≤
      342*model.rat W := by
    change price model (PlayerSpecificAlgebraicCallerFrame.run rows words)≤_
    have hr : rows.length=5 := rfl
    have hw : words.length=4 := rfl
    rw [hr,hw] at hframe
    norm_num at hframe
    exact hframe
  change power.2+numerator.2+
    GeneralPaperRationalPrimitivePrice.binary model.rat (fun u v=>u/v) (numerator.1:ℚ) (power.1:ℚ)+
    price model constant.2+compared.2+
    price model (PlayerSpecificOutputFloorPredicateExecution.frame root a constant.1 threshold P code power.1 numerator.1)≤_
  have hsum:=Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add hpower' hn) (Nat.add_le_add hthreshold hconst'))
    (Nat.add_le_add hcmp hframe')
  have hshape : 256*(P+1)*model.rat W+64*model.rat W+
      (2*model.rat W+8000000000*model.rat W)+
      (PlayerSpecificAlgebraicComparisonExecution.coefficient*(U+1)*model.rat W+
        342*model.rat W)=work T P := by
    dsimp only [work,W,U]
    ring
  simpa only [Nat.add_assoc] using hsum.trans_eq hshape

end Blotto.PlayerSpecificOutputFloorPredicateSourceCost
