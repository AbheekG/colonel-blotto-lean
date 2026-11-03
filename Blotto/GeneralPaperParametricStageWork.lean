import Blotto.GeneralPaperAffineArithmeticStep

/-! The complete native parametric stage with unit rational/index prices.
All feasibility probes execute the actual stored complete-score DP. The
arithmetic bound has no rational-operand width or bit-word factor.
-/
namespace Blotto.GeneralPaperParametricStageWork
open RationalOrderCell GeneralPaperRayAffineScoreStep GeneralPaperRayAffineDPSize GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run {m S K : ℕ} (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) (h : ℕ) (beta : ℚ) (field : Field K) (previous : Table S K) (lo hi : ℚ) :
    Option (GeneralPaperRayCrossingRefinement.Bracket × Table S K) × ℕ :=
  let points := GeneralPaperNativeAffinePrices.crossingsRun (fun _ => 1) 1 field previous
  let refined := GeneralPaperPricedCrossingRefinement.run (fun _ => 1) (fun _ => 1) 1
    (GeneralPaperRayPricedPredicate.query matrix x w S h beta) lo hi points.1
  match refined.bracket with
  | none => (none,points.2+refined.work+8)
  | some b =>
    let midpoint := GeneralPaperRayMidpointPrice.run (fun _ => 1) 1 b.lower b.upper
    let selected := GeneralPaperAffineArithmeticStep.run midpoint.1 field previous
    (some (b,selected.1),points.2+refined.work+midpoint.2+selected.2+16)

theorem data {m S K : ℕ} (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) (h : ℕ) (beta : ℚ) (field : Field K) (previous : Table S K) (lo hi : ℚ) :
    (run matrix x w h beta field previous lo hi).1=
      GeneralPaperRayParametricStage.stage (GeneralPaperRayPricedPredicate.query matrix x w S h beta) field previous lo hi := by
  unfold run GeneralPaperRayParametricStage.stage
  simp only [GeneralPaperNativeAffinePrices.crossings_data,GeneralPaperPricedCrossingRefinement.data]
  cases GeneralPaperRayCrossingRefinement.narrow (GeneralPaperRayPricedPredicate.query matrix x w S h beta)
    lo hi (GeneralPaperRayAffineScoreStep.crossings field previous) <;>
    simp only [GeneralPaperAffineArithmeticStep.data,GeneralPaperRayMidpointPrice.data]

theorem work {m S K : ℕ} (D E X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n+1≤m)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (h : ℕ) (beta : ℚ) (field : Field K) (previous : Table S K)
    (hf : FieldBounded D E X V field) (hp : TableBounded D E X V n previous)
    (lo hi : ℚ) (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P)) :
    (run matrix x w h beta field previous lo hi).2≤
      GeneralPaperParametricStageBits.profile (GeneralPaperRayAffineScoreStep.crossings field previous).length m S K 1 1 := by
  let R := width D E m X V P
  let Q := 4096*(m+1)*(K+1)*(S+1)*(1+1)
  let points := GeneralPaperNativeAffinePrices.crossingsRun (fun _ => 1) 1 field previous
  let query := GeneralPaperRayPricedPredicate.query matrix x w S h beta
  let refined := GeneralPaperPricedCrossingRefinement.run (fun _ => 1) (fun _ => 1) 1 query lo hi points.1
  have hGen := (GeneralPaperNativeAffinePrices.crossings_work (fun _ => 1) (fun _ _ _ => le_rfl)
    1 D E m X V P n hD hE hn field previous hf hp).trans (GeneralPaperNativeAffinePrices.profile_bound S K 1 1)
  have hGen' : points.2≤1024*(S+2)*(K+1)^2*(1+1) := hGen
  have hRoots : ∀ q∈points.1,RationalHeight q R := by
    intro q hq
    rw [GeneralPaperNativeAffinePrices.crossings_data] at hq
    exact GeneralPaperRayUniformSize.stage_roots hD hE hn field previous hf hp q hq
  have hQueries : ∀ q∈GeneralPaperRaySortedCrossings.ordered lo hi points.1,(query q).2≤Q := by
    intro q _
    have hq := GeneralPaperRayPricedPredicate.query_work matrix x w S h beta q
    have hA : 1≤(m+1)*(K+1)*(S+1) := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    change (query q).2≤1024*(m+1)*(K+1)*(S+1)+8 at hq
    dsimp only [Q]
    nlinarith only [hq,hA]
  have hRef := (GeneralPaperPricedCrossingRefinement.arithmetic_work R Q query lo hi points.1 hl hh hRoots hQueries).trans
    (GeneralPaperCrossingPriceEnvelope.refinement_profile points.1.length 1 1 Q)
  have hPoints : points.1=GeneralPaperRayAffineScoreStep.crossings field previous :=
    GeneralPaperNativeAffinePrices.crossings_data _ _ _ _
  rw [←hPoints]
  rw [run]
  change (match refined.bracket with
    | none => (none,points.2+refined.work+8)
    | some b =>
      let midpoint := GeneralPaperRayMidpointPrice.run (fun _ => 1) 1 b.lower b.upper
      let selected := GeneralPaperAffineArithmeticStep.run midpoint.1 field previous
      (some (b,selected.1),points.2+refined.work+midpoint.2+selected.2+16)).2≤_
  cases hr : refined.bracket with
  | none =>
    unfold GeneralPaperParametricStageBits.profile
    dsimp only
    change refined.work≤512*(points.1.length+3)*(binaryWordWidth (points.1.length+3)+2)^2*(1+1)+
      (binaryWordWidth (points.1.length+3)+1)*Q at hRef
    dsimp only [Q] at hRef
    nlinarith only [hGen',hRef,Nat.zero_le (GeneralPaperAffineStepPrice.profile S K 1 1)]
  | some b =>
    have hnarrow : GeneralPaperRayCrossingRefinement.narrow query lo hi points.1=some b := by
      rw [←GeneralPaperPricedCrossingRefinement.data (fun _ => 1) (fun _ => 1) 1]
      exact hr
    have hBounds := GeneralPaperRayBracketSize.narrow_height query lo hi points.1 R hl hh hRoots b hnarrow
    have hMidpoint := GeneralPaperRayMidpointPrice.work (fun _ => 1) (fun _ _ _ => le_rfl)
      1 R b.lower b.upper hBounds.1 hBounds.2
    have hHeight := GeneralPaperRayAffineBound.midpoint_height hBounds.1 hBounds.2
    have hStep := GeneralPaperAffineArithmeticStep.work D E (interceptCap m X P) (slopeCap m V)
      R (2*R+3) hD hE le_rfl ((b.lower+b.upper)/2) hHeight field previous
      (GeneralPaperNativeAffinePrices.field_cap D E m X V P (by omega) field hf)
      (GeneralPaperNativeAffinePrices.table_cap D E m X V P n (by omega) previous hp)
    dsimp only
    change points.2+refined.work+(GeneralPaperRayMidpointPrice.run (fun _ => 1) 1 b.lower b.upper).2+
      (GeneralPaperAffineArithmeticStep.run ((b.lower+b.upper)/2) field previous).2+16≤_
    unfold GeneralPaperParametricStageBits.profile
    change refined.work≤512*(points.1.length+3)*(binaryWordWidth (points.1.length+3)+2)^2*(1+1)+
      (binaryWordWidth (points.1.length+3)+1)*Q at hRef
    dsimp only [Q] at hRef
    nlinarith only [hGen',hRef,hMidpoint,hStep]

end Blotto.GeneralPaperParametricStageWork
