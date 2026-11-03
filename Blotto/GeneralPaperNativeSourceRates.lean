import Blotto.GeneralPaperSourceSoftBounds

/-! Native single-accuracy-power counts and complete DP prices, using the
proved logarithmic source word. Rates retain field and full-code factors;
short grid operands remain polylogarithmic. Zero fields are covered by m+1. -/
namespace Blotto.GeneralPaperNativeSourceRates
open GeneralPaperSourceWordGrowth GeneralPaperNativeSourceWordGrowth
open GeneralPaperSourceSoftBounds GeneralPaperFastRationalModel
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def accuracy (x : Input) : ℕ := 2^x.k
def fields (x : Input) : ℕ := x.m+1
def symbols (x : Input) : ℕ := (alphabet x).lambda+1
def grid (x : Input) : ℕ := (GeneralPaperProfitParameters.prepare x.m (alphabet x).lambda x.k x.Qv).grid.size
def options (x : Input) : ℕ := (GeneralPaperSourceParameters.prepare x.k).summarySize+2

theorem accuracy_positive (x : Input) : 1≤accuracy x := Nat.one_le_pow _ _ (by decide)
theorem fields_positive (x : Input) : 1≤fields x := by unfold fields; omega
theorem symbols_positive (x : Input) : 1≤symbols x := by unfold symbols; omega

theorem grid_rate : Soft accuracy grid := by
  have hM := poly_tight _ measure_tight
  have hP := poly_power _ 2 hM
  apply dominated (poly_mul_rate (poly_mul _ _ (poly_constant (2^34)) hP) (identity accuracy))
  intro x
  exact GeneralPaperFastDPParameterSizes.grid_size _ _ _ _

theorem options_rate : Soft accuracy options :=
  bounded (2^36) (fun x => GeneralPaperFastDPParameterSizes.options x.k)

@[fun_prop]
theorem grid_small : Small grid := grid_size_small

@[fun_prop]
theorem options_small : Small options := by unfold options; fun_prop

@[fun_prop]
theorem short_tight : Tight (fun x => GeneralPaperPowerPreparationEnvelope.operandWidth x.m (alphabet x).lambda x.k x.Qv) := by
  unfold GeneralPaperPowerPreparationEnvelope.operandWidth
  fun_prop

@[fun_prop]
theorem short_small : Small (fun x => GeneralPaperPowerPreparationEnvelope.operandWidth x.m (alphabet x).lambda x.k x.Qv) :=
  of_tight short_tight

@[fun_prop]
theorem short_poly : Polylog (fun x => GeneralPaperPowerPreparationEnvelope.operandWidth x.m (alphabet x).lambda x.k x.Qv) :=
  poly_tight _ short_tight

@[fun_prop]
theorem depth_poly : Polylog (fun x => (GeneralPaperProfitParameters.prepare x.m (alphabet x).lambda x.k x.Qv).grid.depth) :=
  poly_tight _ grid_depth_tight

theorem array_poly (W n : Input → ℕ) (hW : Tight W) (hn : Small n) :
    Polylog (fun x => GeneralPaperSummaryArrayExecution.arrayWord (W x) (n x)) := by
  unfold GeneralPaperSummaryArrayExecution.arrayWord
  fun_prop

theorem plus_one {r n : Input → ℕ} (hr : ∀ x,1≤r x) (hn : Soft r n) : Soft r (fun x => n x+1) :=
  add_same hn (poly_at_rate (poly_constant 1) hr)

theorem empty_rate {r n : Input → ℕ} (hr : ∀ x,1≤r x) (hn : Soft r n) (hs : Small n)
    (W : Input → ℕ) (hW : Tight W) :
    Soft r (fun x => GeneralPaperDPTableControls.emptyProfile (W x) (n x)) := by
  unfold GeneralPaperDPTableControls.emptyProfile
  exact add_same (add_same
    (mul_poly (poly_mul_rate (poly_constant 64) hn) (poly_tight W hW))
    (mul_poly (poly_mul_rate (poly_constant 44) (plus_one hr hn)) (array_poly W n hW hs)))
    (poly_at_rate (poly_mul _ _ (poly_constant 64) (poly_tight W hW)) hr)

theorem labels_rate {r n : Input → ℕ} (hr : ∀ x,1≤r x) (hn : Soft r n) (hs : Small n)
    (W : Input → ℕ) (hW : Tight W) :
    Soft r (fun x => GeneralPaperDPTableControls.labelsProfile (W x) (n x)) := by
  have hp : Polylog (fun x => GeneralPaperSummaryArrayExecution.arrayWord (W x) (n x+2)) :=
    array_poly W _ hW (by fun_prop)
  unfold GeneralPaperDPTableControls.labelsProfile
  exact add_same
    (mul_poly hn (poly_add _ _ (poly_mul _ _ (poly_constant 64) (poly_tight W hW))
      (poly_mul _ _ (poly_constant 72) hp)))
    (poly_at_rate (poly_mul _ _ (poly_constant 18) hp) hr)

theorem query_poly (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Polylog (fun x => GeneralPaperCachedProfitGridPrice.profile (charge C d) (W x) x.m (alphabet x).lambda x.k x.Qv) := by
  change Polylog (fun x => 4096*((GeneralPaperProfitParameters.prepare x.m (alphabet x).lambda x.k x.Qv).grid.depth+1)*
    (W x+charge C d (GeneralPaperPowerPreparationEnvelope.operandWidth x.m (alphabet x).lambda x.k x.Qv)))
  fun_prop

theorem leaf_base_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Soft accuracy (fun x => GeneralPaperOrderedDPAggregatePrice.leafBase (charge C d) (W x)
      x.m (alphabet x).lambda x.k x.Qv (options x) (grid x)) := by
  have hp : Polylog (fun x => GeneralPaperCachedProfitGridPrice.profile (charge C d) (W x) x.m (alphabet x).lambda x.k x.Qv+
      384*W x+128*GeneralPaperSummaryArrayExecution.arrayWord (W x) (grid x)) := by
    have hq := query_poly C d W hW
    have ha := array_poly W grid hW grid_small
    fun_prop
  unfold GeneralPaperOrderedDPAggregatePrice.leafBase
  exact add_same (add_same (add_same (empty_rate accuracy_positive grid_rate grid_small W hW)
    (labels_rate accuracy_positive options_rate options_small W hW)) (mul_poly options_rate hp))
    (poly_at_rate (by fun_prop) accuracy_positive)

theorem merge_base_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Soft (fun x => (accuracy x)^2) (fun x => GeneralPaperOrderedDPAggregatePrice.mergeBase (charge C d) (W x)
      x.m (alphabet x).lambda x.k x.Qv (grid x)) := by
  have hpos (x : Input) : 1≤(accuracy x)^2 := Nat.one_le_pow _ _ (accuracy_positive x)
  have hincl (x : Input) : accuracy x≤(accuracy x)^2 := by
    have h := accuracy_positive x
    nlinarith only [h]
  have hq := query_poly C d W hW
  have ha := array_poly W grid hW grid_small
  have hp : Polylog (fun x => GeneralPaperCachedProfitGridPrice.profile (charge C d) (W x) x.m (alphabet x).lambda x.k x.Qv+
      2*charge C d (GeneralPaperPowerPreparationEnvelope.operandWidth x.m (alphabet x).lambda x.k x.Qv)+576*W x+
      256*GeneralPaperSummaryArrayExecution.arrayWord (W x) (grid x)) := by fun_prop
  have hrow : Soft accuracy (fun x => grid x*(GeneralPaperCachedProfitGridPrice.profile (charge C d) (W x) x.m (alphabet x).lambda x.k x.Qv+
      2*charge C d (GeneralPaperPowerPreparationEnvelope.operandWidth x.m (alphabet x).lambda x.k x.Qv)+576*W x+
      256*GeneralPaperSummaryArrayExecution.arrayWord (W x) (grid x))+128*W x) :=
    add_same (mul_poly grid_rate hp) (poly_at_rate (by fun_prop) accuracy_positive)
  have hgrid : Soft (fun x => (accuracy x)^2) (fun x => grid x*(grid x*(GeneralPaperCachedProfitGridPrice.profile (charge C d) (W x) x.m (alphabet x).lambda x.k x.Qv+
      2*charge C d (GeneralPaperPowerPreparationEnvelope.operandWidth x.m (alphabet x).lambda x.k x.Qv)+576*W x+
      256*GeneralPaperSummaryArrayExecution.arrayWord (W x) (grid x))+128*W x)) := by
    simpa only [_root_.pow_two] using mul grid_rate hrow
  unfold GeneralPaperOrderedDPAggregatePrice.mergeBase
  exact add_same (add_same (add_same (rate_mono (empty_rate accuracy_positive grid_rate grid_small W hW) hincl)
    (rate_mono (labels_rate accuracy_positive grid_rate grid_small W hW) hincl)) hgrid)
    (poly_at_rate (by fun_prop) hpos)

end Blotto.GeneralPaperNativeSourceRates
