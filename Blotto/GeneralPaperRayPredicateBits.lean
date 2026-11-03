import Blotto.GeneralPaperRayQueryWidth

/-! The actual native feasibility predicate with complete fixed-probe bit
prices. Cost construction, complete-score DP, strict minimum scan and weak
budget comparison are all included. Root/lattice premises come from the
native stage; source integer/reference/control capacities remain explicit.
-/
namespace Blotto.GeneralPaperRayPredicateBits
open RationalOrderCell GeneralPaperExactScoreDP GeneralPaperRayRationalBound
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 4096

def compareRun {K : ℕ} (model : RationalCostModel) (W : ℕ) (beta : ℚ) :
    Option (GeneralPaperMinimum.Selection K) → Bool × ℕ
  | none => (true,8*W)
  | some chosen => (decide (beta≤chosen.cost),8*W+model.rat (RationalExpression.pairWidth beta chosen.cost))

def run {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (Field K))
    (x w : Variable m K → ℚ) (S h : ℕ) (beta t : ℚ) : Bool × ℕ :=
  let minimum := GeneralPaperRayMinimumBits.run model W matrix x w t S h
  let accepted := compareRun model W beta minimum.1
  (accepted.1,minimum.2+accepted.2)

theorem data {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (Field K))
    (x w : Variable m K → ℚ) (S h : ℕ) (beta t : ℚ) :
    (run model W matrix x w S h beta t).1=(GeneralPaperRayPricedPredicate.query matrix x w S h beta t).1 := by
  simp only [run,GeneralPaperRayMinimumBits.data,GeneralPaperRayPricedPredicate.query]
  cases (GeneralPaperRayQueryWork.minimumRun matrix x w t S h).1 <;> rfl

theorem actual_data {T m K : ℕ} (model : RationalCostModel) (W scoreDepth : ℕ)
    (d : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m) (S : ℕ)
    (hK : 0<K) (hCap : S<2^scoreDepth) (x w : Variable m K → ℚ) (h : ℕ) (beta t : ℚ) :
    (run model W (GeneralPaperScoreMatrixWork.matrixRun scoreDepth d v S).1 x w S h beta t).1=
      GeneralPaperRayFeasibility.test v S h beta x w t := by
  rw [data]
  exact GeneralPaperRayPricedPredicate.actual_data scoreDepth d v S hK hCap x w h beta t

theorem work {m K : ℕ} (model : RationalCostModel) (W D E X V P s : ℕ) (hD : 0<D) (hED : E∣D)
    (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ)
    (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E V (w a))
    (beta : ℚ) (hb : Bounded D P beta) (t : ℚ) (ht : 0≤t ∧ t≤1) (hT : RationalHeight t s) (S h : ℕ)
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth (S+2)≤W) :
    (run model W matrix x w S h beta t).2≤4096*(m+1)*(K+1)*(S+1)*
      (W+model.rat (1+2*(GeneralPaperRayUniformSize.width D E m X V P+s))) := by
  let H := 1+2*(GeneralPaperRayUniformSize.width D E m X V P+s)
  let Q := model.rat H
  let A := (m+1)*(K+1)*(S+1)
  let minimum := GeneralPaperRayMinimumBits.run model W matrix x w t S h
  have hBase := GeneralPaperRayMinimumBits.work model W D E X V hD hED matrix x w hx hw t ht S h hW hK hM hIndex
  have hWord := GeneralPaperRayQueryWidth.width (m:=m) (D:=D) (E:=E) (X:=X) (V:=V) (P:=P) t hT
  have hMono := GeneralPaperRayMinimumBits.profile_mono m K S W (model.monotone hWord)
  have hCap := GeneralPaperRayMinimumBits.profile_bound m K S W Q hW
  have hMinimum : minimum.2≤2048*A*(W+Q) := by
    simpa only [A,Nat.mul_assoc] using (hBase.trans hMono).trans hCap
  have hCompare : (compareRun model W beta minimum.1).2≤8*W+Q := by
    cases hr : minimum.1 with
    | none => simp only [compareRun]; omega
    | some chosen =>
      have hn : (GeneralPaperRayQueryWork.minimumRun matrix x w t S h).1=some chosen := by
        rw [←GeneralPaperRayMinimumBits.data model W]
        exact hr
      have ho := GeneralPaperRayComparisonOperandSize.predicate hD hED matrix x w hx hw beta hb t ht hT S h chosen hn
      have hp := model.monotone (max_le (rationalWordWidth_of_height ho.1) (rationalWordWidth_of_height ho.2))
      change model.rat (RationalExpression.pairWidth beta chosen.cost)≤Q at hp
      change 8*W+model.rat (RationalExpression.pairWidth beta chosen.cost)≤_
      exact Nat.add_le_add_left hp _
  have hA : 1≤A := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have hSmall := Nat.mul_le_mul_right (W+Q) hA
  simp only [Nat.one_mul] at hSmall
  change minimum.2+(compareRun model W beta minimum.1).2≤4096*(m+1)*(K+1)*(S+1)*(W+Q)
  dsimp only [A] at hMinimum hSmall
  nlinarith only [hMinimum,hCompare,hSmall,Nat.zero_le ((m+1)*(K+1)*(S+1)*(W+Q))]

end Blotto.GeneralPaperRayPredicateBits
