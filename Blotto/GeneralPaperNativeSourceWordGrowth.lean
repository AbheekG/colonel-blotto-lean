import Blotto.GeneralPaperConstructedWordGrowth

/-! Concrete selected-source parameters have the logarithmic word bounds
needed for a source-wide reference calibration. Alphabet, rounded-value
and budget facts come from native constructors and actual input witnesses.
The source horizon is not enumerated or reconstructed by these observers. -/
namespace Blotto.GeneralPaperNativeSourceWordGrowth
open GeneralPaperSourceWordGrowth GeneralPaperConstructedWordGrowth
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

@[fun_prop]
theorem period_small : Small (fun x => (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).period) := by
  simp only [GeneralPaperTrajectoryParameters.period_power]
  fun_prop

@[fun_prop]
theorem epochs_small : Small (fun x => (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs) := by
  apply dominated (g:=fun x => 2*(((alphabet x).lambda+2)*2^(35+x.k)))
  · fun_prop
  · intro x
    exact (GeneralPaperTrajectoryParameters.epochs_upper _ _).le

@[fun_prop]
theorem rows_small : Small (fun x => (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows) := by
  simp only [GeneralPaperTrajectoryParameters.rows_product]
  fun_prop

@[fun_prop]
theorem summary_small : Small (fun x => (GeneralPaperSourceParameters.prepare x.k).summarySize) := by
  have he : (fun x : Input => (GeneralPaperSourceParameters.prepare x.k).summarySize)=(fun x => 2^(34+x.k)) :=
    funext (fun x => (GeneralPaperSourceParameters.data x.k).2.2.2.2.2)
  rw [he]
  fun_prop

@[fun_prop]
theorem mesh_small : Small (fun x => (GeneralPaperSourceParameters.prepare x.k).meshDenominator) := by
  have he : (fun x : Input => (GeneralPaperSourceParameters.prepare x.k).meshDenominator)=(fun x => 2^(29+x.k)) :=
    funext (fun x => (GeneralPaperSourceParameters.data x.k).2.2.2.2.1)
  rw [he]
  fun_prop

@[fun_prop]
theorem profit_height_tight : Tight (fun x => (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).height) := by
  dsimp only [GeneralPaperProfitParameters.parameters]
  fun_prop

@[fun_prop]
theorem profit_height_small : Small (fun x => (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).height) :=
  of_tight profit_height_tight

@[fun_prop]
theorem profit_leaves_small : Small (fun x => (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).leafCount) := by
  dsimp only [GeneralPaperProfitParameters.parameters]
  fun_prop

@[fun_prop]
theorem profit_q_small : Small (fun x => (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).qProf) := by
  simp only [GeneralPaperProfitParameters.qProf_spec]
  fun_prop

@[fun_prop]
theorem profit_width_small : Small (fun x => (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).width) := by
  dsimp only [GeneralPaperProfitParameters.parameters]
  fun_prop

@[fun_prop]
theorem profit_exponent_tight : Tight (fun x => (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).exponent) := by
  dsimp only [GeneralPaperProfitParameters.parameters]
  fun_prop

@[fun_prop]
theorem profit_exponent_small : Small (fun x => (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).exponent) :=
  of_tight profit_exponent_tight

@[fun_prop]
theorem grid_size_small : Small (fun x => (GeneralPaperProfitParameters.prepare x.m (alphabet x).lambda x.k x.Qv).grid.size) := by
  apply dominated (g:=fun x => GeneralPaperFastDPParameterSizes.gridCap x.m (alphabet x).lambda x.k x.Qv)
  · fun_prop [GeneralPaperFastDPParameterSizes.gridCap]
  · intro x
    exact GeneralPaperFastDPParameterSizes.grid_size _ _ _ _

@[fun_prop]
theorem grid_depth_tight : Tight (fun x => (GeneralPaperProfitParameters.prepare x.m (alphabet x).lambda x.k x.Qv).grid.depth) := by
  refine ⟨64,?_⟩
  intro x
  have hm : GeneralPaperSourcePreparationSizes.measure x.m (alphabet x).lambda x.k x.Qv≤logSize x := by
    dsimp only [GeneralPaperSourcePreparationSizes.measure,logSize]
    omega
  exact (GeneralPaperFastDPParameterSizes.grid_depth _ _ _ _).trans (Nat.mul_le_mul_left 64 hm)

@[fun_prop]
theorem grid_depth_small : Small (fun x => (GeneralPaperProfitParameters.prepare x.m (alphabet x).lambda x.k x.Qv).grid.depth) :=
  of_tight grid_depth_tight

@[fun_prop]
theorem precision_bits_tight : Tight (fun x => (GeneralPaperPowerPrecision.prepare (alphabet x).lambda x.k).fractionalBits) := by
  refine ⟨128,?_⟩
  intro x
  have h := (GeneralPaperSourcePreparationControls.metadata x.m (alphabet x).lambda x.k x.Qv).fractionalBits
  have hm : GeneralPaperSourcePreparationSizes.measure x.m (alphabet x).lambda x.k x.Qv≤logSize x := by
    dsimp only [GeneralPaperSourcePreparationSizes.measure,logSize]
    omega
  exact h.trans (Nat.mul_le_mul_left 128 hm)

@[fun_prop]
theorem precision_bits_small : Small (fun x => (GeneralPaperPowerPrecision.prepare (alphabet x).lambda x.k).fractionalBits) :=
  of_tight precision_bits_tight

@[fun_prop]
theorem precision_columns_tight : Tight (fun x => (GeneralPaperPowerPrecision.prepare (alphabet x).lambda x.k).columns) := by
  refine ⟨32,?_⟩
  intro x
  have h := (GeneralPaperSourcePreparationControls.metadata x.m (alphabet x).lambda x.k x.Qv).columns
  have hm : GeneralPaperSourcePreparationSizes.measure x.m (alphabet x).lambda x.k x.Qv≤logSize x := by
    dsimp only [GeneralPaperSourcePreparationSizes.measure,logSize]
    omega
  exact h.trans (Nat.mul_le_mul_left 32 hm)

@[fun_prop]
theorem precision_columns_small : Small (fun x => (GeneralPaperPowerPrecision.prepare (alphabet x).lambda x.k).columns) :=
  of_tight precision_columns_tight

@[fun_prop]
theorem precision_unit_small : Small (fun x => (GeneralPaperPowerPrecision.prepare (alphabet x).lambda x.k).unit) := by
  simp only [GeneralPaperPowerPrecision.unit_power]
  fun_prop

@[fun_prop]
theorem original_budget_word_small : Small (fun x => rationalWordWidth x.b) := by
  apply dominated (g:=fun x => 1+2*x.B)
  · fun_prop
  · intro x
    exact rationalWordWidth_of_height x.hB

@[fun_prop]
theorem own_budget_word_small : Small (fun x => rationalWordWidth (GeneralPaperInitializerPreparedPoint.ownBudget x.m x.k (x.b:ℝ) x.reciprocal)) := by
  apply dominated (g:=fun x => 1+2*((alphabet x).lambda+1))
  · fun_prop
  · intro x
    exact GeneralPaperSourceBudgetWidths.own_word _ _ _ (by exact_mod_cast x.hb) _

@[fun_prop]
theorem opposing_budget_word_small : Small (fun x => rationalWordWidth (GeneralPaperInitializerPreparedPoint.opposingBudget x.m x.k (x.b:ℝ) x.reciprocal)) := by
  apply dominated (g:=fun x => 1+2*((alphabet x).lambda+1))
  · fun_prop
  · intro x
    exact GeneralPaperSourceBudgetWidths.opposing_word _ _ _ (by exact_mod_cast x.hb) _

@[fun_prop]
theorem weight_array_small (W : ℕ) : Small (fun x => GeneralPaperEncodedNatArray.footprint W x.weights) := by
  apply dominated (g:=fun x => x.m*(1+binaryWordWidth x.Qv+W)+32*W)
  · fun_prop
  · intro x
    exact GeneralPaperEncodedNatArray.bounded W _ x.weights (fun j => Nat.add_le_add_left
      (binaryWordWidth_mono (GeneralPaperSourceScoreHeights.weight_le x.Qv x.weights x.weight_sum j)) 1)

end Blotto.GeneralPaperNativeSourceWordGrowth
