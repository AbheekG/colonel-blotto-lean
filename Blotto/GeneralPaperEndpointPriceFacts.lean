import Blotto.GeneralPaperEndpointPriceControl

/-! Static probe size and unit interval are consequences of the original
rows and native feasible start/unit coordinate velocity. They are not
endpoint, bit-size or query truth oracles supplied to the priced algorithm.
-/
namespace Blotto.GeneralPaperEndpointPriceFacts
open RationalOrderCell GeneralPaperRayUniformSize GeneralPaperRayRationalBound GeneralPaperStaticRayRows
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem zero_height (D E m X V P : ℕ) : RationalHeight (0:ℚ) (width D E m X V P) := by
  apply GeneralPaperQuantizedHeight.zero_height
  have hp := binaryWordWidth_pos D
  unfold width GeneralPaperRayAffineBound.rootWidth
  omega

theorem static_height {T m K : ℕ} (primitive : ℕ → ℕ) (W D E X V P : ℕ) (hm : 0<m) (hD : 0<D) (hE : 0<E)
    (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (x w : Variable m K → ℚ) (hx : ∀ a,Bounded D X (x a)) (hw : ∀ a,Bounded E V (w a))
    (h : ℕ) (beta : ℚ) (hb : Bounded D P beta) (c : GeneralPaperRayMinimum.Choice (StaticIndex T m K))
    (hs : (GeneralPaperStaticScanPrice.run primitive W labels x w).choice=some c) :
    RationalHeight c.time (width D E m X V P) := by
  apply static_time hm hD hE labels (GeneralPaperRayQueryWork.scores matrix) h beta x w hx hw hb c
  simpa only [GeneralPaperStaticScanPrice.data] using hs

theorem static_interval {T m K : ℕ} (primitive : ℕ → ℕ) (W : ℕ)
    (labels : Fin T → Fin m → Fin K) (matrix : FixedArrayTable m (GeneralPaperExactScoreDP.Field K))
    (h : ℕ) (beta : ℚ) (x w : Variable m K → ℚ)
    (hStart : GeneralPaperAffineConstraintRows.Feasible labels (GeneralPaperRayQueryWork.scores matrix) h
      (beta:ℝ) (fun j => (x j:ℝ))) (next : Variable m K) (hVelocity : w next=1)
    (c : GeneralPaperRayMinimum.Choice (StaticIndex T m K))
    (hs : (GeneralPaperStaticScanPrice.run primitive W labels x w).choice=some c) : 0≤c.time ∧ c.time≤1 := by
  obtain ⟨out,ho,hlo,hhi,_⟩ := GeneralPaperStaticRaySound.finite_endpoint labels
    (GeneralPaperRayQueryWork.scores matrix) h (beta:ℝ) x w hStart next hVelocity
  have hc : out=c := by
    have hn : (GeneralPaperStaticRayScan.scan labels x w).choice=some c := by
      simpa only [GeneralPaperStaticScanPrice.data] using hs
    exact Option.some.inj (ho.symm.trans hn)
  simpa only [hc] using And.intro hlo hhi

end Blotto.GeneralPaperEndpointPriceFacts
