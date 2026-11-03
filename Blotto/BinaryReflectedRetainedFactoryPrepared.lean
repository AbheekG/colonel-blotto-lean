import Blotto.BinaryReflectedCachedCertifiedResult
import Blotto.BinaryReflectedCachedTerminalInput
import Blotto.BinaryReflectedFactoryPrepared

/-! A reached reflected factory consumes the retained setup/capacity cache.
One cached terminal input/permutation supplies the actual full nested table,
which is retained for choice/emission. Exact table and factory prices match the
old producer, while terminal capacity production is charged by the prefix. -/

namespace Blotto.BinaryReflectedRetainedFactoryPrepared
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedFourSetup
open BinarySharedResourceRun BinaryReflectedSerialRun

def prepareTerminal (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (cached : BinaryReflectedSetupCache.Prepared input) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) (K : ℕ) (outer : Fin K → Bool) :
    BinaryReflectedFactoryPrepared.Prepared input result.state K outer :=
  let assembled := BinaryReflectedCachedTerminalInput.Prepared.terminalWithWork cached result.state
  let factory := BinaryNestedSpecFactoryWork.profileWithWork assembled.1.1 K outer
  let table := BinaryTerminalProfileCompiler.permute factory.1 assembled.1.2
  have hTable : table = BinaryTerminalProfileCompiler.profile (prepare input) result.state K outer := by
    unfold table
    rw [BinaryNestedSpecFactoryWork.profileWithWork_state,BinaryReflectedCachedTerminalInput.terminalWithWork_original]
    rfl
  ⟨⟨table,(by rw [hTable]; exact BinaryTerminalProfileCompiler.profile_canonical _ result.state (prepare_canonical input hC) result.canonical K outer),
    (by rw [hTable]; exact profile_nonnegative input hC hAd N bits result hSuccess K outer),hTable,assembled.2⟩,factory.2⟩

theorem prepareTerminal_base (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (cached : BinaryReflectedSetupCache.Prepared input) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) (K : ℕ) (outer : Fin K → Bool) :
    (prepareTerminal input hC hAd cached N bits result hSuccess K outer).toPrepared =
      { (BinaryReflectedFactoryPrepared.prepareTerminal input hC hAd N bits result hSuccess K outer).toPrepared with
        inputWork := (BinaryReflectedCachedTerminalInput.Prepared.terminalWithWork cached result.state).2 } := by
  unfold prepareTerminal BinaryReflectedFactoryPrepared.prepareTerminal
  simp only [BinaryNestedSpecFactoryWork.profileWithWork_state,BinaryReflectedCachedTerminalInput.terminalWithWork_original,
    BinaryNestedTerminalPreparationWork.prepareWithWork_state]

theorem draw_ignores_inputWork {input : BinaryFourParameters.Input} {state : BinaryThreeResourceState.State}
    {K : ℕ} {outer : Fin K → Bool} (prepared : BinaryReflectedPreparedDraw.Prepared input state K outer)
    (work : ℕ) (N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    ({ prepared with inputWork := work }.runIndexedWithWork N scalar bits pos hp) =
      prepared.runIndexedWithWork N scalar bits pos hp := rfl

theorem prepareTerminal_factoryWork (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (cached : BinaryReflectedSetupCache.Prepared input) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) (K : ℕ) (outer : Fin K → Bool) :
    (prepareTerminal input hC hAd cached N bits result hSuccess K outer).factoryWork =
      (BinaryReflectedFactoryPrepared.prepareTerminal input hC hAd N bits result hSuccess K outer).factoryWork := by
  unfold prepareTerminal BinaryReflectedFactoryPrepared.prepareTerminal
  simp only [BinaryReflectedCachedTerminalInput.terminalWithWork_original,BinaryNestedTerminalPreparationWork.prepareWithWork_state]

theorem prepareTerminal_inputWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (hAd : Admissible input) (cached : BinaryReflectedSetupCache.Prepared input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (N : ℕ) (bits : Fin N → Bool) (result : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) (K : ℕ) (outer : Fin K → Bool) :
    (prepareTerminal input hC hAd cached N bits result hSuccess K outer).toPrepared.inputWork ≤
      BinaryNestedTerminalPreparationWork.bound (expressionHeightBudget s 21) := by
  have hEq := BinaryReflectedCachedTerminalInput.terminalWithWork_prefix_price cached result.state
  rw [cached.system_correct] at hEq
  have hBound := BinaryNestedTerminalPreparationWork.reached_bound input source hC hR hCase s hs hH N bits result hSuccess
  change (BinaryReflectedCachedTerminalInput.Prepared.terminalWithWork cached result.state).2 ≤ _
  omega

theorem prepareTerminal_factoryWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (hAd : Admissible input) (cached : BinaryReflectedSetupCache.Prepared input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (N : ℕ) (bits : Fin N → Bool) (result : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) (K : ℕ) (outer : Fin K → Bool) :
    (prepareTerminal input hC hAd cached N bits result hSuccess K outer).factoryWork ≤ BinaryReflectedFactoryPrepared.bound s K := by
  rw [prepareTerminal_factoryWork]
  exact BinaryReflectedFactoryPrepared.prepareTerminal_factoryWork_bound input source hC hR hCase hAd s hs hH N bits result hSuccess K outer

end Blotto.BinaryReflectedRetainedFactoryPrepared
