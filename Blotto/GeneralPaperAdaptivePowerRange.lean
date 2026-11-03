import Blotto.GeneralPaperAdaptiveEpochHistory

/-! The adaptive level cap implies that the actual stored powers stay in
[1/2,1] within an epoch. Thus the native numerator conversion uses the two
proved adjacent exponents; positivity alone is not substituted for its exact
normalization contract.
-/
namespace Blotto.GeneralPaperAdaptivePowerRange
open scoped BigOperators
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperEpochFieldState GeneralPaperEpochSnapshot GeneralPaperAdaptiveEpoch
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem exact_power_range (lambda k time degree : ℕ)
    (hTime : time≤(GeneralPaperTrajectoryParameters.prepare lambda k).period)
    (hDegree : degree≤time*(8*(GeneralPaperSourceParameters.prepare k).meshDenominator)) :
    (31/32:ℝ)≤(GeneralPaperCachedMassJoin.base k:ℝ)^degree ∧ (GeneralPaperCachedMassJoin.base k:ℝ)^degree≤1 := by
  let eta : ℝ := (GeneralPaperSourceParameters.prepare k).eta
  let theta : ℝ := (GeneralPaperSourceParameters.prepare k).theta
  let N : ℝ := (GeneralPaperSourceParameters.prepare k).meshDenominator
  have hp := GeneralPaperSourceParameters.positive k
  have hb := GeneralPaperGeometricLevels.base_bounds _ _ hp.2.1 hp.2.2.2 (GeneralPaperSourceParameters.eta_theta k)
  have hb0 : (0:ℝ)≤GeneralPaperCachedMassJoin.base k := by
    have hq : (0:ℚ)≤GeneralPaperCachedMassJoin.base k := by
      change 0≤GeneralPaperGeometricLevels.geometricBase _ _
      linarith [hb.1]
    exact_mod_cast hq
  have hb1 : (GeneralPaperCachedMassJoin.base k:ℝ)≤1 := by exact_mod_cast hb.2.le
  have hStep : 0≤1-(GeneralPaperCachedMassJoin.base k:ℝ) := by linarith
  have hd : (degree:ℝ)≤(time:ℝ)*(8*N) := by dsimp only [N]; exact_mod_cast hDegree
  have hN : 0<N := by dsimp only [N]; exact_mod_cast GeneralPaperSourceParameters.mesh_positive k
  have htN : theta*N=1 := by
    dsimp only [theta,N]
    rw [GeneralPaperSourceParameters.theta_mesh]
    push_cast
    have hn : ((GeneralPaperSourceParameters.prepare k).meshDenominator:ℝ)≠0 := ne_of_gt hN
    field_simp [hn]
  have hEq : (1-(GeneralPaperCachedMassJoin.base k:ℝ))*((time:ℝ)*(8*N))=4*eta*time := by
    calc
      _ = 4*eta*time*(theta*N) := by
        dsimp only [GeneralPaperCachedMassJoin.base,GeneralPaperGeometricLevels.geometricBase,eta,theta]
        push_cast
        ring
      _ = _ := by rw [htN,mul_one]
  have he := mul_le_mul_of_nonneg_left hd hStep
  rw [hEq] at he
  have hr := GeneralPaperEpochCDF.epoch_rate lambda k time hTime
  have hl := GeneralPaperGeometricVariation.power_lower (GeneralPaperCachedMassJoin.base k:ℝ) hb0 hb1 degree
  exact ⟨by dsimp only [eta] at he; linarith, pow_le_one₀ hb0 hb1⟩

theorem stored_power_range (lambda k time degree : ℕ)
    (hTime : time≤(GeneralPaperTrajectoryParameters.prepare lambda k).period)
    (hDegree : degree≤time*(8*(GeneralPaperSourceParameters.prepare k).meshDenominator)) :
    (1/2:ℚ)≤GeneralPaperDyadicFloat.value (GeneralPaperPreparedPowers.query (GeneralPaperPreparedPowers.prepare lambda k) degree).number ∧
      GeneralPaperDyadicFloat.value (GeneralPaperPreparedPowers.query (GeneralPaperPreparedPowers.prepare lambda k) degree).number≤1 := by
  have hCap := hDegree.trans (GeneralPaperEpochFieldStep.epoch_cap lambda k time hTime)
  have hError := GeneralPaperPreparedPowers.query_error lambda k degree hCap
  change |(GeneralPaperCachedMassJoin.base k:ℝ)^degree-_|≤_ at hError
  have he := abs_le.mp hError
  have hc := (GeneralPaperPreparedPowers.query_certificate lambda k degree hCap).2.2.2.2
  have hr := exact_power_range lambda k time degree hTime hDegree
  have hNu : ((GeneralPaperSourceParameters.prepare k).nu:ℝ)≤1 := by
    have heta := GeneralPaperSourceParameters.eta_upper k
    have hnu := GeneralPaperSourceParameters.nu_eta k
    have hq : (GeneralPaperSourceParameters.prepare k).nu≤1 := by rw [hnu]; linarith
    exact_mod_cast hq
  have hLow : (1/2:ℝ)≤(GeneralPaperDyadicFloat.value
      (GeneralPaperPreparedPowers.query (GeneralPaperPreparedPowers.prepare lambda k) degree).number:ℝ) := by
    linarith
  have hHigh : (GeneralPaperDyadicFloat.value
      (GeneralPaperPreparedPowers.query (GeneralPaperPreparedPowers.prepare lambda k) degree).number:ℝ)≤1 := by
    have hCast : (GeneralPaperDyadicFloat.value
        (GeneralPaperPreparedPowers.query (GeneralPaperPreparedPowers.prepare lambda k) degree).number:ℝ)≤
        (GeneralPaperCachedMassJoin.base k:ℝ)^degree := by exact_mod_cast hc
    exact hCast.trans hr.2
  constructor
  · have hl : ((1/2:ℚ):ℝ)≤(GeneralPaperDyadicFloat.value
        (GeneralPaperPreparedPowers.query (GeneralPaperPreparedPowers.prepare lambda k) degree).number:ℝ) := by
      norm_num
      exact hLow
    exact_mod_cast hl
  · exact_mod_cast hHigh

theorem block_numerator_bounds (lambda k time : ℕ) (levels : Summary k)
    (hTime : time≤(GeneralPaperTrajectoryParameters.prepare lambda k).period)
    (hLevels : ∀ r, levels.read r≤time*(8*(GeneralPaperSourceParameters.prepare k).meshDenominator))
    (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    (GeneralPaperPreparedPowers.prepare lambda k).format.unit≤(block (GeneralPaperPreparedPowers.prepare lambda k) levels).values.read r ∧
      (block (GeneralPaperPreparedPowers.prepare lambda k) levels).values.read r≤2*(GeneralPaperPreparedPowers.prepare lambda k).format.unit := by
  change _≤(GeneralPaperEpochPowerQueries.buildNumerators _ levels).read r ∧
    (GeneralPaperEpochPowerQueries.buildNumerators _ levels).read r≤_
  rw [GeneralPaperEpochPowerQueries.read_numerators]
  have hCap := (hLevels r).trans (GeneralPaperEpochFieldStep.epoch_cap lambda k time hTime)
  have hr := stored_power_range lambda k time _ hTime (hLevels r)
  exact GeneralPaperLocalPowerNumerators.numerator_bounds _ _ (GeneralPaperPowerPrecision.unit_power lambda k) _
    (GeneralPaperPreparedPowers.query_certificate lambda k _ hCap).2.1 hr.1 hr.2

theorem snapshot_numerator_bounds (lambda k time : ℕ) (state : State k)
    (hTime : time≤(GeneralPaperTrajectoryParameters.prepare lambda k).period)
    (hState : Bounded state (time*(8*(GeneralPaperSourceParameters.prepare k).meshDenominator))) :
    let snap := take (GeneralPaperPreparedPowers.prepare lambda k) state
    let unit := (GeneralPaperPreparedPowers.prepare lambda k).format.unit
    (∀ r, unit≤snap.p.values.read r ∧ snap.p.values.read r≤2*unit) ∧
    (∀ r, unit≤snap.q.values.read r ∧ snap.q.values.read r≤2*unit) ∧
    (∀ r, unit≤snap.lambda.values.read r ∧ snap.lambda.values.read r≤2*unit) ∧
    (∀ r, unit≤snap.mu.values.read r ∧ snap.mu.values.read r≤2*unit) :=
  ⟨block_numerator_bounds lambda k time state.pOccurrences hTime hState.1,
    block_numerator_bounds lambda k time state.qOccurrences hTime hState.2.1,
    block_numerator_bounds lambda k time state.lambdaOccurrences hTime hState.2.2.1,
    block_numerator_bounds lambda k time state.muOccurrences hTime hState.2.2.2.1⟩

end Blotto.GeneralPaperAdaptivePowerRange
