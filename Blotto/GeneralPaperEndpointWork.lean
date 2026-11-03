import Blotto.GeneralPaperEndpointPriceFacts

/-! Complete native endpoint execution in the unit real-RAM model. All
rational and index primitives have unit price. The one-time static list,
all residuals/comparisons, one static feasibility probe, conditional full
high search and branch/answer construction are included.
-/
namespace Blotto.GeneralPaperEndpointWork
open RationalOrderCell GeneralPaperRayUniformSize GeneralPaperRayRationalBound
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run {T m K : ℕ} (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h : ℕ) (beta : ℚ)
    (x w : Variable m K → ℚ) : Option (GeneralPaperRayEndpoint.Answer T m K) × ℕ :=
  GeneralPaperEndpointPriceControl.run 1 (GeneralPaperStaticScanPrice.run (fun _ => 1) 1 labels x w)
    (GeneralPaperRayPricedPredicate.query matrix x w S h beta)
    (GeneralPaperHighSearchWork.run matrix x w S h beta)

theorem data {T m K : ℕ} (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h : ℕ) (beta : ℚ) (x w : Variable m K → ℚ) :
    (run labels matrix S h beta x w).1=GeneralPaperRayEndpoint.prepared labels matrix S h beta x w := by
  apply GeneralPaperEndpointPriceControl.data _ _ _ _ labels matrix x w S h beta
  · exact GeneralPaperStaticScanPrice.data _ _ _ _ _
  · exact fun _ => rfl
  · exact GeneralPaperHighSearchWork.data matrix x w S h beta

theorem actual_data {T m K : ℕ} (scoreDepth : ℕ) (d : GeneralPaperDictionary.Dictionary T m K)
    (v : RationalFieldSelector m) (S h : ℕ) (beta : ℚ) (x w : Variable m K → ℚ) :
    (run d.label (GeneralPaperScoreMatrixWork.matrixRun scoreDepth d v S).1 S h beta x w).1=
      GeneralPaperRayEndpoint.execute scoreDepth d v S h beta x w := data _ _ _ _ _ _ _

theorem work {T m K : ℕ} (D E X V P : ℕ) (hm : 0<m) (hK : 2≤K) (hD : 0<D) (hE : 0<E)
    (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (S h : ℕ) (beta : ℚ) (x w : Variable m K → ℚ)
    (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E V (w a)) (hb : Bounded D P beta) :
    (run labels matrix S h beta x w).2≤GeneralPaperEndpointPriceControl.profile T m K S 1 1 := by
  let static := GeneralPaperStaticScanPrice.run (fun _ => 1) 1 labels x w
  let query := GeneralPaperRayPricedPredicate.query matrix x w S h beta
  let high := GeneralPaperHighSearchWork.run matrix x w S h beta
  have hStatic : static.work≤8192*(m*(K-1)+m*T+1)*(1+1) :=
    GeneralPaperStaticScanPrice.work_linear (fun _ => 1) (fun _ _ _ => le_rfl) 1 D E X V P hm hK hD hE labels x w hx hw
  have hQuery : ∀ c,static.choice=some c → (query c.time).2≤4096*(m+1)*(K+1)*(S+1)*(1+1) := by
    intro c _
    have hq := GeneralPaperRayPricedPredicate.query_work matrix x w S h beta c.time
    have hA : 1≤(m+1)*(K+1)*(S+1) := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    nlinarith only [hq,hA]
  have hHigh : ∀ c,static.choice=some c → (high 0 c.time).2≤GeneralPaperHighSearchPriceFacts.profile m S K 1 1 := by
    intro c hc
    have hs := GeneralPaperEndpointPriceFacts.static_height (fun _ => 1) 1 D E X V P hm hD hE
      labels matrix x w hx hw h beta hb c hc
    exact GeneralPaperHighSearchWork.work D E X V P hD hE matrix x w hx hw S h beta hb 0 c.time
      (GeneralPaperEndpointPriceFacts.zero_height D E m X V P) hs
  exact GeneralPaperEndpointPriceControl.work 1 _ _ _ static query high hStatic hQuery hHigh

end Blotto.GeneralPaperEndpointWork
