import Blotto.GeneralPaperNativeSegmentFactoryLifetime

/-! Reference scaling and address capacity of the complete segment-factory
phase profile. This analysis-level word reserves a scaling borrowed owner;
the whole-preparation common word and its construction remain separate. -/
namespace Blotto.GeneralPaperSegmentFactoryReferenceScaling
open GeneralPaperReferenceScaling
attribute [local fun_prop] GeneralPaperExpressionRowLifetime.profile_scale
set_option autoImplicit false
set_option maxHeartbeats 2000000

@[fun_prop]
theorem matrix_time (model : RationalCostModel) (n r k s d M : ℕ) :
    Scale (fun A => GeneralPaperExpressionMatrixLifetime.matrixTime model A n r k s d M) := by
  unfold GeneralPaperExpressionMatrixLifetime.matrixTime
  fun_prop

@[fun_prop]
theorem compiler_time (model : RationalCostModel) (n r k s d M : ℕ) :
    Scale (fun A => GeneralPaperSegmentCompilerStorage.compilerTime model A n r k s d M) := by
  unfold GeneralPaperSegmentCompilerStorage.compilerTime GeneralPaperSegmentExpressionCompiler.bound
    GeneralPaperExpressionRowLifetime.callbackTime
  fun_prop

@[fun_prop]
theorem outer_profile (model : RationalCostModel) (n r k s d M : ℕ) :
    Scale (fun A => GeneralPaperExpressionMatrixLifetime.outerProfile model A n r k s d M) := by
  unfold GeneralPaperExpressionMatrixLifetime.outerProfile GeneralPaperEncodedBasisStorage.arrayProfile
  fun_prop

@[fun_prop]
theorem compiler_profile (model : RationalCostModel) (n r k s d M : ℕ) (borrowed : ℕ → ℕ) (hb : Scale borrowed) :
    Scale (fun A => GeneralPaperSegmentCompilerLifetime.profile model A n r k s d M (borrowed A)) := by
  unfold GeneralPaperSegmentCompilerLifetime.profile GeneralPaperSegmentCompilerStorage.rowOwnerProfile
    GeneralPaperSegmentCompilerStorage.matrixOwnerProfile GeneralPaperExpressionRowLifetime.profile
    GeneralPaperExpressionRowLifetime.callbackTime GeneralPaperExpressionArrayReturns.rowProfile
    GeneralPaperExpressionArrayReturns.matrixProfile GeneralPaperExpressionMatrixLifetime.activeProfile
    GeneralPaperSegmentCompilerStorage.assemblyProfile GeneralPaperEncodedBasisStorage.arrayProfile
  fun_prop

@[fun_prop]
theorem environment_time (k s : ℕ) : Scale (fun A => GeneralPaperFixedEnvironmentLifetime.time A k s) := by
  unfold GeneralPaperFixedEnvironmentLifetime.time
  fun_prop

@[fun_prop]
theorem environment_profile (k s : ℕ) (borrowed : ℕ → ℕ) (hb : Scale borrowed) :
    Scale (fun A => GeneralPaperFixedEnvironmentLifetime.profile A k s (borrowed A)) := by
  unfold GeneralPaperFixedEnvironmentLifetime.profile GeneralPaperEncodedBasisStorage.arrayProfile
  fun_prop

@[fun_prop]
theorem cap_scale (model : RationalCostModel) (n r k s d M : ℕ) :
    Scale (fun A => GeneralPaperFixedSegmentFactoryLifetime.cap model A n r k s d M) := by
  unfold GeneralPaperFixedSegmentFactoryLifetime.cap
  fun_prop

@[fun_prop]
theorem controls_profile (model : RationalCostModel) (n r k s d M : ℕ) :
    Scale (fun A => GeneralPaperFixedSegmentFactoryLifetime.controlProfile model A n r k s d M) := by
  unfold GeneralPaperFixedSegmentFactoryLifetime.controlProfile
  fun_prop

@[fun_prop]
theorem factory_profile (model : RationalCostModel) (n r k s d M : ℕ) (borrowed : ℕ → ℕ) (hb : Scale borrowed) :
    Scale (fun A => GeneralPaperFixedSegmentFactoryLifetime.profile model A n r k s d M (borrowed A)) := by
  unfold GeneralPaperFixedSegmentFactoryLifetime.profile GeneralPaperSegmentCompilerStorage.assemblyProfile
    GeneralPaperEncodedBasisStorage.arrayProfile
  fun_prop

@[fun_prop]
theorem selector_time (model : RationalCostModel) (s : ℕ) :
    Scale (fun A => GeneralPaperUniformSegmentPreparation.bound model A s) := by
  unfold GeneralPaperUniformSegmentPreparation.bound GeneralPaperPairSegmentPreparation.bound
    GeneralPaperThreeSegmentPreparation.bound GeneralPaperSegmentExpressionCompiler.bound
    GeneralPaperExpressionBitExecution.nodeBound GeneralPaperExpressionBitExecution.unit
  fun_prop

theorem native_profile (model : RationalCostModel) (s : ℕ) (borrowed : ℕ → ℕ) (hb : Scale borrowed) :
    Scale (fun A => GeneralPaperNativeSegmentFactoryLifetime.profile model A s (borrowed A)) := by
  unfold GeneralPaperNativeSegmentFactoryLifetime.profile GeneralPaperNativeSegmentFactoryLifetime.selectorProfile
  fun_prop

def reference (model : RationalCostModel) (s : ℕ) (borrowed : ℕ → ℕ) : ℕ :=
  GeneralPaperReferenceCapacity.referenceWord (GeneralPaperNativeSegmentFactoryLifetime.profile model 1 s (borrowed 1))

theorem capacity (model : RationalCostModel) (s : ℕ) (borrowed : ℕ → ℕ) (hb : Scale borrowed) :
    GeneralPaperNativeSegmentFactoryLifetime.profile model (reference model s borrowed) s (borrowed (reference model s borrowed)) <
      2 ^ reference model s borrowed :=
  GeneralPaperReferenceCapacity.profile_capacity _ (native_profile model s borrowed hb)

theorem actual_capacity {m : ℕ} (i : RationalUniformGroupSpec m) (size : ℕ) (hSize : size = m) (hm : m = 2 ∨ m = 3)
    (model : RationalCostModel) (s : ℕ) (hs : 2 ≤ s) (h : i.FieldsHeight s)
    (borrowed : ℕ → ℕ) (hb : Scale borrowed) (phase : GeneralPaperNativeSegmentFactoryLifetime.Phase m) :
    let A := reference model s borrowed
    GeneralPaperNativeSegmentFactoryLifetime.window i size hm model A (borrowed A) phase < 2 ^ A :=
  (GeneralPaperNativeSegmentFactoryLifetime.bounded i size hSize hm model _ s _ hs h phase).trans_lt
    (capacity model s borrowed hb)

theorem native_capacity {n : ℕ} (bits : Bool) (model : RationalCostModel) (W exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded bits model W exponent values v hv).weight j ≤ 1)
    (p : RationalTerminalPacking (GeneralPaperEqualFiniteKernel.terminal
      (GeneralPaperEqualNativeSampler.rounded bits model W exponent values v hv) small))
    (borrowed : ℕ → ℕ) (hb : Scale borrowed)
    (phase : GeneralPaperNativeSegmentFactoryLifetime.Phase (GeneralPaperEqualFiniteKernel.terminal
      (GeneralPaperEqualNativeSampler.rounded bits model W exponent values v hv) small).groups.length) :
    let A := reference model (GeneralPaperEqualNativeSampler.fieldHeight n exponent) borrowed
    GeneralPaperNativeSegmentFactoryLifetime.window
      (p.uniformSpec (GeneralPaperEqualFiniteKernel.no_fraction _ small)) p.groups.data.size
      (GeneralPaperEqualFiniteKernel.terminal _ small).groups_count model A (borrowed A) phase < 2 ^ A := by
  dsimp only
  exact (GeneralPaperNativeSegmentFactoryLifetime.native bits model W _ exponent values v hv small p _ phase).trans_lt
    (capacity model (GeneralPaperEqualNativeSampler.fieldHeight n exponent) borrowed hb)

end Blotto.GeneralPaperSegmentFactoryReferenceScaling
