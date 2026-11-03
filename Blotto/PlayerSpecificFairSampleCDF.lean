import Blotto.PlayerSpecificOriginalFieldCDF

/-! Exact CDF events and pathwise downward-displacement sandwiches for
two samples using the same complete fair packet. -/
namespace Blotto.PlayerSpecificFairSampleCDF
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem cdf {N : ℕ} (R : ℕ) (draw : (Fin R → Bool) → Allocation N) (j : Fin N) (z : ℝ) :
    closedCDF ((fairBitLaw R).map draw) j z=(fairBitLaw R : Measure (Fin R → Bool)).real {bits | draw bits j ≤ z} := by
  change (Measure.map (fun y : Allocation N => y j) (Measure.map draw (fairBitLaw R : Measure (Fin R → Bool)))).real (Set.Iic z)=_
  rw [Measure.map_map (measurable_pi_apply j) (measurable_of_countable _),
    map_measureReal_apply (measurable_of_countable _) measurableSet_Iic]
  rfl

theorem negative {N : ℕ} (R : ℕ) (draw : (Fin R → Bool) → Allocation N) (j : Fin N) (z : ℝ)
    (hn : ∀ bits,0 ≤ draw bits j) (hz : z < 0) : closedCDF ((fairBitLaw R).map draw) j z=0 := by
  have he : {bits | draw bits j ≤ z}=(∅ : Set (Fin R → Bool)) := by
    ext bits
    simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
    intro h
    linarith only [hn bits,hz,h]
  rw [cdf R draw j z,he,measureReal_empty]

theorem sandwich {N : ℕ} (R : ℕ) (original rounded : (Fin R → Bool) → Allocation N) (d : ℝ)
    (hdown : ∀ bits j,rounded bits j ≤ original bits j)
    (hgap : ∀ bits j,original bits j-rounded bits j ≤ d) (j : Fin N) (z : ℝ) :
    closedCDF ((fairBitLaw R).map original) j z ≤ closedCDF ((fairBitLaw R).map rounded) j z ∧
      closedCDF ((fairBitLaw R).map rounded) j z ≤ closedCDF ((fairBitLaw R).map original) j (z+d) := by
  constructor
  · rw [cdf R original j z,cdf R rounded j z]
    apply measureReal_mono (μ := (fairBitLaw R : Measure (Fin R → Bool))) ?_ (measure_ne_top _ _)
    intro bits hb
    exact (hdown bits j).trans hb
  · rw [cdf R rounded j z,cdf R original j (z+d)]
    apply measureReal_mono (μ := (fairBitLaw R : Measure (Fin R → Bool))) ?_ (measure_ne_top _ _)
    intro bits hb
    have hg := hgap bits j
    change original bits j ≤ z+d
    change rounded bits j ≤ z at hb
    linarith only [hg,hb]

end Blotto.PlayerSpecificFairSampleCDF
