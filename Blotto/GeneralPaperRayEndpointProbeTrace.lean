import Blotto.GeneralPaperRayParametricProbeTrace

/-! Exact erased complete-score query trace of the native endpoint branch:
one actual static probe and, only on rejection, the actual high-search
query traces. Fixed affine-table recovery does not rerun the complete DP. -/
namespace Blotto.GeneralPaperRayEndpointProbeTrace
open RationalOrderCell GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 8192

def run {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (labels : Fin T → Fin m → Fin K)
    (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K)) (S h : ℕ) (beta : ℚ)
    (x w : Variable m K → ℚ) : List ℚ :=
  match (GeneralPaperStaticScanPrice.run model.rat W labels x w).choice with
  | none => []
  | some c => c.time::if (GeneralPaperRayPredicateBits.run model W matrix x w S h beta c.time).1=true then []
      else GeneralPaperRayParametricProbeTrace.high model W matrix x w S h beta 0 c.time

theorem bounded {T m K : ℕ} (model : RationalCostModel) (W D E X V P : ℕ) (hD : 0<D) (hE : 0<E)
    (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (S h : ℕ) (beta : ℚ) (x w : Variable m K → ℚ)
    (hx : ∀ a,GeneralPaperRayRationalBound.Bounded D X (x a)) (hw : ∀ a,GeneralPaperRayRationalBound.Bounded E V (w a))
    (hb : GeneralPaperRayRationalBound.Bounded D P beta)
    (c : GeneralPaperRayMinimum.Choice (GeneralPaperStaticRayRows.StaticIndex T m K))
    (hScan : (GeneralPaperStaticScanPrice.run model.rat W labels x w).choice=some c)
    (hLo : 0≤c.time) (hHi : c.time≤1) (hHeight : RationalHeight c.time (width D E m X V P))
    (t : ℚ) (ht : t∈run model W labels matrix S h beta x w) :
    0≤t ∧ t≤1 ∧ RationalHeight t (width D E m X V P) := by
  rw [run,hScan] at ht
  rcases List.mem_cons.mp ht with rfl|ht
  · exact ⟨hLo,hHi,hHeight⟩
  · by_cases ha : (GeneralPaperRayPredicateBits.run model W matrix x w S h beta c.time).1=true
    · simp only [ha,ite_true,List.not_mem_nil] at ht
    · simp only [ha] at ht
      have hs := GeneralPaperRayParametricProbeTrace.high_bounded model W D E X V P hD hE matrix x w hx hw S h beta hb
        0 c.time hLo (GeneralPaperEndpointPriceFacts.zero_height D E m X V P) hHeight t ht
      exact ⟨hs.1,hs.2.1.trans hHi,hs.2.2⟩

end Blotto.GeneralPaperRayEndpointProbeTrace
