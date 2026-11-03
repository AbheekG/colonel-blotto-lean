import Blotto.GeneralPaperRayMidpointPrice

/-! Complete native parametric stage: generate its actual pair batch, narrow
with the actual complete-score DP, construct the rational midpoint and build
the selected affine layer. The output equals the existing stage exactly.
-/
namespace Blotto.GeneralPaperParametricStageBits
open RationalOrderCell GeneralPaperRayAffineScoreStep GeneralPaperRayAffineDPSize GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run {m S K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) (h : ℕ) (beta : ℚ) (field : Field K) (previous : Table S K) (lo hi : ℚ) :
    Option (GeneralPaperRayCrossingRefinement.Bracket × Table S K) × ℕ :=
  let points := GeneralPaperNativeAffinePrices.crossingsRun model.rat W field previous
  let refined := GeneralPaperRayBitRefinement.run model W matrix x w S h beta lo hi points.1
  match refined.bracket with
  | none => (none,points.2+refined.work+8*W)
  | some b =>
    let midpoint := GeneralPaperRayMidpointPrice.run model.rat W b.lower b.upper
    let selected := GeneralPaperAffineStepPrice.run model.rat W midpoint.1 field previous
    (some (b,selected.1),points.2+refined.work+midpoint.2+selected.2+16*W)

theorem data {m S K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) (h : ℕ) (beta : ℚ) (field : Field K) (previous : Table S K) (lo hi : ℚ) :
    (run model W matrix x w h beta field previous lo hi).1=
      GeneralPaperRayParametricStage.stage (GeneralPaperRayPricedPredicate.query matrix x w S h beta) field previous lo hi := by
  unfold run GeneralPaperRayParametricStage.stage
  simp only [GeneralPaperNativeAffinePrices.crossings_data,GeneralPaperRayBitRefinement.data]
  cases GeneralPaperRayCrossingRefinement.narrow (GeneralPaperRayPricedPredicate.query matrix x w S h beta)
    lo hi (GeneralPaperRayAffineScoreStep.crossings field previous) <;>
    simp only [GeneralPaperAffineStepPrice.data,GeneralPaperRayMidpointPrice.data]

def profile (n m S K W P : ℕ) : ℕ :=
  1024*(S+2)*(K+1)^2*(W+P)+512*(n+3)*(binaryWordWidth (n+3)+2)^2*(P+W)+
    (binaryWordWidth (n+3)+1)*(4096*(m+1)*(K+1)*(S+1)*(W+P))+
    GeneralPaperAffineStepPrice.profile S K W P+32*W+5*P

theorem work {m S K : ℕ} (model : RationalCostModel) (W D E X V P n : ℕ)
    (hD : 0<D) (hE : 0<E) (hED : E∣D) (hn : n+1≤m)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (x w : Variable m K → ℚ)
    (hx : ∀ a,GeneralPaperRayRationalBound.Bounded D X (x a))
    (hw : ∀ a,GeneralPaperRayRationalBound.Bounded E V (w a)) (h : ℕ) (beta : ℚ)
    (hb : GeneralPaperRayRationalBound.Bounded D P beta) (field : Field K) (previous : Table S K)
    (hf : FieldBounded D E X V field) (hp : TableBounded D E X V n previous)
    (lo hi : ℚ) (hLo : 0≤lo) (hOrder : lo≤hi) (hHi : hi≤1)
    (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P))
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth (S+2)≤W) (hBatch : binaryWordWidth ((S+1)*(K*K)+3)≤W) :
    (run model W matrix x w h beta field previous lo hi).2≤
      profile (GeneralPaperRayAffineScoreStep.crossings field previous).length m S K W
        (model.rat (6*width D E m X V P+9)) := by
  let R := width D E m X V P
  let Q := model.rat (6*R+9)
  let points := GeneralPaperNativeAffinePrices.crossingsRun model.rat W field previous
  let refined := GeneralPaperRayBitRefinement.run model W matrix x w S h beta lo hi points.1
  have hSmall := model.monotone (show 1+2*R≤6*R+9 by omega)
  have hQuery := model.monotone (show 1+4*R≤6*R+9 by omega)
  have hMid := model.monotone (show 4*R+7≤6*R+9 by omega)
  have hGen := (GeneralPaperNativeAffinePrices.crossings_work model.rat model.monotone W D E m X V P n
    hD hE hn field previous hf hp).trans (GeneralPaperNativeAffinePrices.profile_bound S K W (model.rat (1+2*R)))
  have hGen' : points.2≤1024*(S+2)*(K+1)^2*(W+Q) := by
    apply hGen.trans
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_left hSmall W)
  have hRoots : ∀ q∈points.1,RationalHeight q R := by
    intro q hq
    rw [GeneralPaperNativeAffinePrices.crossings_data] at hq
    exact GeneralPaperRayUniformSize.stage_roots hD hE hn field previous hf hp q hq
  have hLen : points.1.length≤(S+1)*(K*K) := by
    rw [GeneralPaperNativeAffinePrices.crossings_data]
    exact GeneralPaperRayAffineScoreStep.crossings_length field previous
  have hBatch' := (binaryWordWidth_mono (Nat.add_le_add_right hLen 3)).trans hBatch
  have hRef := GeneralPaperRayBitRefinement.work model W D E X V P hD hED matrix x w hx hw beta hb S h lo hi points.1
    hLo hOrder hHi hl hh hRoots hW hK hM hIndex hBatch'
  have hRef' : refined.work≤512*(points.1.length+3)*(binaryWordWidth (points.1.length+3)+2)^2*(Q+W)+
      (binaryWordWidth (points.1.length+3)+1)*(4096*(m+1)*(K+1)*(S+1)*(W+Q)) := by
    apply hRef.trans
    exact Nat.add_le_add
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right hSmall W))
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.add_le_add_left hQuery W)))
  have hPoints : points.1=GeneralPaperRayAffineScoreStep.crossings field previous :=
    GeneralPaperNativeAffinePrices.crossings_data _ _ _ _
  rw [←hPoints]
  change _≤profile points.1.length m S K W Q
  rw [run]
  change (match refined.bracket with
    | none => (none,points.2+refined.work+8*W)
    | some b =>
      let midpoint := GeneralPaperRayMidpointPrice.run model.rat W b.lower b.upper
      let selected := GeneralPaperAffineStepPrice.run model.rat W midpoint.1 field previous
      (some (b,selected.1),points.2+refined.work+midpoint.2+selected.2+16*W)).2≤_
  cases hr : refined.bracket with
  | none =>
    unfold profile
    dsimp only
    nlinarith only [hGen',hRef',Nat.zero_le (GeneralPaperAffineStepPrice.profile S K W Q)]
  | some b =>
    have hnarrow : GeneralPaperRayCrossingRefinement.narrow
        (GeneralPaperRayPricedPredicate.query matrix x w S h beta) lo hi points.1=some b := by
      rw [←GeneralPaperRayBitRefinement.data model W]
      exact hr
    have hBounds := GeneralPaperRayBracketSize.narrow_height _ lo hi points.1 R hl hh hRoots b hnarrow
    have hMidpoint := GeneralPaperRayMidpointPrice.work model.rat model.monotone W R b.lower b.upper hBounds.1 hBounds.2
    have hMidpoint' : (GeneralPaperRayMidpointPrice.run model.rat W b.lower b.upper).2≤16*W+5*Q := by
      nlinarith only [hMidpoint,hMid]
    have hHeight := GeneralPaperRayAffineBound.midpoint_height hBounds.1 hBounds.2
    have hStep := GeneralPaperNativeAffinePrices.step_work model.rat model.monotone W D E m X V P n hD hE hn
      ((b.lower+b.upper)/2) hHeight field previous hf hp hW hIndex
    dsimp only
    change points.2+refined.work+(GeneralPaperRayMidpointPrice.run model.rat W b.lower b.upper).2+
      (GeneralPaperAffineStepPrice.run model.rat W ((b.lower+b.upper)/2) field previous).2+16*W≤_
    unfold profile
    nlinarith only [hGen',hRef',hMidpoint',hStep]

end Blotto.GeneralPaperParametricStageBits
