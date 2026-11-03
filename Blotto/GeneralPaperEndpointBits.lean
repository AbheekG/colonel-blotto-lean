import Blotto.GeneralPaperEndpointWork

/-! Complete native static-or-high endpoint in the paper fast-bit model.
Native lattices bound actual rational operands; original feasibility and
the next coordinate velocity derive the static probe interval. Index,
score and reference word capacities remain explicit global obligations.
-/
namespace Blotto.GeneralPaperEndpointBits
open RationalOrderCell GeneralPaperRayUniformSize GeneralPaperRayRationalBound
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 4096

def run {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h : ℕ) (beta : ℚ)
    (x w : Variable m K → ℚ) : Option (GeneralPaperRayEndpoint.Answer T m K) × ℕ :=
  GeneralPaperEndpointPriceControl.run W (GeneralPaperStaticScanPrice.run model.rat W labels x w)
    (GeneralPaperRayPredicateBits.run model W matrix x w S h beta)
    (GeneralPaperHighSearchBits.run model W matrix x w S h beta)

theorem data {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h : ℕ) (beta : ℚ) (x w : Variable m K → ℚ) :
    (run model W labels matrix S h beta x w).1=GeneralPaperRayEndpoint.prepared labels matrix S h beta x w := by
  apply GeneralPaperEndpointPriceControl.data _ _ _ _ labels matrix x w S h beta
  · exact GeneralPaperStaticScanPrice.data _ _ _ _ _
  · exact GeneralPaperRayPredicateBits.data model W matrix x w S h beta
  · exact GeneralPaperHighSearchBits.data model W matrix x w S h beta

theorem actual_data {T m K : ℕ} (model : RationalCostModel) (W scoreDepth : ℕ)
    (d : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m) (S h : ℕ)
    (beta : ℚ) (x w : Variable m K → ℚ) :
    (run model W d.label (GeneralPaperScoreMatrixWork.matrixRun scoreDepth d v S).1 S h beta x w).1=
      GeneralPaperRayEndpoint.execute scoreDepth d v S h beta x w := data model W _ _ _ _ _ _ _

theorem work {T m K : ℕ} (model : RationalCostModel) (W D E X V P : ℕ)
    (hD : 0<D) (hE : 0<E) (hED : E∣D) (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h : ℕ) (beta : ℚ)
    (x w : Variable m K → ℚ) (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E V (w a)) (hb : Bounded D P beta)
    (hStart : GeneralPaperAffineConstraintRows.Feasible labels (GeneralPaperRayQueryWork.scores matrix) h
      (beta:ℝ) (fun j => (x j:ℝ))) (next : Variable m K) (hVelocity : w next=1)
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth (S+2)≤W) (hBatch : binaryWordWidth ((S+1)*(K*K)+3)≤W)
    (hFinalIndex : binaryWordWidth (S+4)≤W) :
    (run model W labels matrix S h beta x w).2≤
      GeneralPaperEndpointPriceControl.profile T m K S W (model.rat (6*width D E m X V P+9)) := by
  let R := width D E m X V P
  let Q := model.rat (6*R+9)
  let static := GeneralPaperStaticScanPrice.run model.rat W labels x w
  let query := GeneralPaperRayPredicateBits.run model W matrix x w S h beta
  let high := GeneralPaperHighSearchBits.run model W matrix x w S h beta
  have hm : 0<m := Nat.zero_lt_of_lt next.1.isLt
  have hTwo : 2≤K := by have hh := next.2.isLt; omega
  have hStatic : static.work≤8192*(m*(K-1)+m*T+1)*(W+Q) := by
    have hh := GeneralPaperStaticScanPrice.work_linear model.rat model.monotone W D E X V P hm hTwo hD hE labels x w hx hw
    have hp := model.monotone (show 1+2*R≤6*R+9 by omega)
    exact hh.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left hp W))
  have hQuery : ∀ c,static.choice=some c → (query c.time).2≤4096*(m+1)*(K+1)*(S+1)*(W+Q) := by
    intro c hc
    have hs := GeneralPaperEndpointPriceFacts.static_height model.rat W D E X V P hm hD hE
      labels matrix x w hx hw h beta hb c hc
    have ht := GeneralPaperEndpointPriceFacts.static_interval model.rat W labels matrix h beta x w hStart next hVelocity c hc
    have hq := GeneralPaperRayPredicateBits.work model W D E X V P R hD hED matrix x w hx hw beta hb c.time ht hs S h hW hK hM hIndex
    have hp := model.monotone (show 1+2*(R+R)≤6*R+9 by omega)
    exact hq.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left hp W))
  have hHigh : ∀ c,static.choice=some c → (high 0 c.time).2≤GeneralPaperHighSearchPriceFacts.profile m S K W Q := by
    intro c hc
    have hs := GeneralPaperEndpointPriceFacts.static_height model.rat W D E X V P hm hD hE
      labels matrix x w hx hw h beta hb c hc
    have ht := GeneralPaperEndpointPriceFacts.static_interval model.rat W labels matrix h beta x w hStart next hVelocity c hc
    exact GeneralPaperHighSearchBits.work model W D E X V P hD hE hED matrix x w hx hw S h beta hb 0 c.time
      le_rfl ht.1 ht.2 (GeneralPaperEndpointPriceFacts.zero_height D E m X V P) hs hW hK hM hIndex hBatch hFinalIndex
  exact GeneralPaperEndpointPriceControl.work W _ _ _ static query high hStatic hQuery hHigh

end Blotto.GeneralPaperEndpointBits
