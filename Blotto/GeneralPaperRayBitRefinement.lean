import Blotto.GeneralPaperRayPredicateBits

/-! Discharge the crossing-refinement query price with the actual complete
score predicate. All queries are built and run on demand at stored crossings.
The result is exactly the native adjacent bracket; no query-cost oracle is
assumed. The explicit paper word-capacity premises are still retained.
-/
namespace Blotto.GeneralPaperRayBitRefinement
open RationalOrderCell GeneralPaperExactScoreDP GeneralPaperRayRationalBound
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 4096

theorem narrow_congr (first second : ℚ → Bool × ℕ) (h : ∀ t,(first t).1=(second t).1)
    (lo hi : ℚ) (points : List ℚ) :
    GeneralPaperRayCrossingRefinement.narrow first lo hi points=
      GeneralPaperRayCrossingRefinement.narrow second lo hi points := by
  unfold GeneralPaperRayCrossingRefinement.narrow
  have he : (GeneralPaperRaySearchControls.selected (fun i => first
      ((GeneralPaperRaySortedCrossings.array lo hi points).read i))).rank=
      (GeneralPaperRaySearchControls.selected (fun i => second
        ((GeneralPaperRaySortedCrossings.array lo hi points).read i))).rank :=
    GeneralPaperPricedRaySearch.oracle_rank_congr _ _ (fun i => h _) _ _ _ _
  simp only [he]

def run {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (Field K))
    (x w : Variable m K → ℚ) (S h : ℕ) (beta lo hi : ℚ) (points : List ℚ) :
    GeneralPaperPricedCrossingRefinement.Result :=
  GeneralPaperPricedCrossingRefinement.run model.rat (fun w => w) W
    (GeneralPaperRayPredicateBits.run model W matrix x w S h beta) lo hi points

theorem data {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (Field K))
    (x w : Variable m K → ℚ) (S h : ℕ) (beta lo hi : ℚ) (points : List ℚ) :
    (run model W matrix x w S h beta lo hi points).bracket=
      GeneralPaperRayCrossingRefinement.narrow
        (GeneralPaperRayPricedPredicate.query matrix x w S h beta) lo hi points := by
  rw [run,GeneralPaperPricedCrossingRefinement.data]
  exact narrow_congr _ _ (GeneralPaperRayPredicateBits.data model W matrix x w S h beta) lo hi points

theorem probes {m K : ℕ} (model : RationalCostModel) (W : ℕ) (matrix : FixedArrayTable m (Field K))
    (x w : Variable m K → ℚ) (S h : ℕ) (beta lo hi : ℚ) (points : List ℚ) :
    (run model W matrix x w S h beta lo hi points).probes≤binaryWordWidth (points.length+3)+1 :=
  GeneralPaperPricedCrossingRefinement.probes _ _ _ _ _ _ _

theorem work {m K : ℕ} (model : RationalCostModel) (W D E X V P : ℕ) (hD : 0<D) (hED : E∣D)
    (matrix : FixedArrayTable m (Field K)) (x w : Variable m K → ℚ)
    (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E V (w a))
    (beta : ℚ) (hb : Bounded D P beta) (S h : ℕ) (lo hi : ℚ) (points : List ℚ)
    (hLo : 0≤lo) (hOrder : lo≤hi) (hHi : hi≤1)
    (hl : RationalHeight lo (GeneralPaperRayUniformSize.width D E m X V P))
    (hh : RationalHeight hi (GeneralPaperRayUniformSize.width D E m X V P))
    (hp : ∀ q∈points,RationalHeight q (GeneralPaperRayUniformSize.width D E m X V P))
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (hIndex : binaryWordWidth (S+2)≤W) (hBatch : binaryWordWidth (points.length+3)≤W) :
    (run model W matrix x w S h beta lo hi points).work≤
      512*(points.length+3)*(binaryWordWidth (points.length+3)+2)^2*
        (model.rat (1+2*GeneralPaperRayUniformSize.width D E m X V P)+W)+
      (binaryWordWidth (points.length+3)+1)*
        (4096*(m+1)*(K+1)*(S+1)*
          (W+model.rat (1+4*GeneralPaperRayUniformSize.width D E m X V P))) := by
  let R := GeneralPaperRayUniformSize.width D E m X V P
  let Q := 4096*(m+1)*(K+1)*(S+1)*(W+model.rat (1+4*R))
  have hQueries : ∀ q∈GeneralPaperRaySortedCrossings.ordered lo hi points,
      (GeneralPaperRayPredicateBits.run model W matrix x w S h beta q).2≤Q := by
    intro q hq
    have hInterval := GeneralPaperRaySortedCrossings.ordered_bound lo hi hOrder points q hq
    have hHeight : RationalHeight q R := by
      rcases (GeneralPaperRaySortedCrossings.ordered_mem lo hi points q).mp hq with he|he|⟨hq,_,_⟩
      · rw [he]; exact hl
      · rw [he]; exact hh
      · exact hp q hq
    have hc := GeneralPaperRayPredicateBits.work model W D E X V P R hD hED matrix x w hx hw
      beta hb q ⟨hLo.trans hInterval.1,hInterval.2.trans hHi⟩ hHeight S h hW hK hM hIndex
    change _≤4096*(m+1)*(K+1)*(S+1)*(W+model.rat (1+2*(R+R))) at hc
    have he : 1+2*(R+R)=1+4*R := by ring
    rw [he] at hc
    exact hc
  have hc := GeneralPaperPricedCrossingRefinement.bit_work model W R Q
    (GeneralPaperRayPredicateBits.run model W matrix x w S h beta) lo hi points hW hBatch hl hh hp hQueries
  exact hc.trans (GeneralPaperCrossingPriceEnvelope.refinement_profile points.length W (model.rat (1+2*R)) Q)

end Blotto.GeneralPaperRayBitRefinement
