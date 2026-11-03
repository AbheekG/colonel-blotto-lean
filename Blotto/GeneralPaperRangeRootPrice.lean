import Blotto.GeneralPaperRangeUpdateArithmetic

/-! Integer instruction endpoints are cast once at the update root. The
already-retained shared span is passed through unchanged; no power, source
parameter or level-validation pass is executed. Code effects derive the
output cap required by the complete traversal's native-data/unit-price join.
-/
namespace Blotto.GeneralPaperRangeRootPrice
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperGlobalNodeQuery
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def run (bits : Bool) (price : ℕ → ℕ) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (lo hi amount height : ℕ) (n : Node height) (span : ℚ) : GeneralPaperIntervalUpdate.Result height × ℕ :=
  let p := if bits then price else fun _ => 1
  let found := GeneralPaperRangeUpdateExecution.run bits price W c (lo:ℚ) hi amount height n 0 span
  (found.1,found.2+p (rationalWordWidth (lo:ℚ))+p (rationalWordWidth (hi:ℚ))+64*W)

theorem data (bits : Bool) (price : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (lo hi amount height : ℕ) (n : Node height) (span : ℚ) (hValid : Valid lambda k n)
    (hOutput : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0
      (GeneralPaperIntervalUpdate.run c.powers (lo:ℚ) hi amount height n 0 span).node) :
    (run bits price W c lo hi amount height n span).1=GeneralPaperIntervalUpdate.run c.powers (lo:ℚ) hi amount height n 0 span :=
  GeneralPaperRangeUpdateExecution.data bits price W m lambda k Qv c hc (lo:ℚ) hi amount height n 0 span hValid hOutput

theorem grid_output_path (m lambda k Qv : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (lo hi amount height : ℕ) (n : Node height) (span : ℚ) (hSpan : span=(2:ℚ)^height)
    (hFinal : ∀ i<2^height,levelAt n i+(if lo ≤ i ∧ i < hi then amount else 0)≤GeneralPaperPowerPrecision.levelBound lambda k) :
    PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0
      (GeneralPaperIntervalUpdate.run c.powers (lo:ℚ) hi amount height n 0 span).node := by
  have hp : c.powers=GeneralPaperPreparedPowers.prepare lambda k := by rw [hc]; rfl
  rw [hp,hSpan]
  exact GeneralPaperRangeUpdateState.output_path_from_effect lambda k lo hi amount height 0 n
    (by simpa only [Nat.zero_add] using hFinal)

theorem grid_data (bits : Bool) (price : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (lo hi amount height : ℕ) (n : Node height) (span : ℚ) (hSpan : span=(2:ℚ)^height) (hValid : Valid lambda k n)
    (hFinal : ∀ i<2^height,levelAt n i+(if lo ≤ i ∧ i < hi then amount else 0)≤GeneralPaperPowerPrecision.levelBound lambda k) :
    (run bits price W c lo hi amount height n span).1=GeneralPaperIntervalUpdate.run c.powers (lo:ℚ) hi amount height n 0 span :=
  data bits price W m lambda k Qv c hc lo hi amount height n span hValid
    (grid_output_path m lambda k Qv c hc lo hi amount height n span hSpan hFinal)

theorem arithmetic_work (price : ℕ → ℕ) (m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (lo hi amount height : ℕ) (n : Node height) (span : ℚ) (hSpan : span=(2:ℚ)^height) (hValid : Valid lambda k n)
    (hFinal : ∀ i<2^height,levelAt n i+(if lo ≤ i ∧ i < hi then amount else 0)≤GeneralPaperPowerPrecision.levelBound lambda k) :
    (run false price 1 c lo hi amount height n span).2≤
      (1+4*height)*GeneralPaperRangeUpdateArithmetic.nodeProfile m lambda k Qv+66 := by
  have hs : 0<span := by rw [hSpan]; positivity
  have hp := grid_output_path m lambda k Qv c hc lo hi amount height n span hSpan hFinal
  have h := GeneralPaperRangeUpdateArithmetic.linear_work price m lambda k Qv c hc (lo:ℚ) hi amount height n 0 span hs hValid hp
  exact Nat.add_le_add_right h 66

theorem same_data (price : ℕ → ℕ) (W m lambda k Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (lo hi amount height : ℕ) (n : Node height) (span : ℚ) (hSpan : span=(2:ℚ)^height) (hValid : Valid lambda k n)
    (hFinal : ∀ i<2^height,levelAt n i+(if lo ≤ i ∧ i < hi then amount else 0)≤GeneralPaperPowerPrecision.levelBound lambda k) :
    (run true price W c lo hi amount height n span).1=(run false price 1 c lo hi amount height n span).1 := by
  rw [grid_data true price W m lambda k Qv c hc lo hi amount height n span hSpan hValid hFinal,
    grid_data false price 1 m lambda k Qv c hc lo hi amount height n span hSpan hValid hFinal]

end Blotto.GeneralPaperRangeRootPrice
