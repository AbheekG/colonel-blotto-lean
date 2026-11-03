import Blotto.BinaryNestedSpecFactoryWork
import Blotto.BinaryReflectedPreparedDraw

/-! A reached reflected terminal builds the measured full nested factory once,
permutes that same table, then reuses it for selection/emission. Factory work is
derived from original six-word source heights and actual resource success. -/

namespace Blotto.BinaryReflectedFactoryPrepared
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedFourSetup
open BinarySharedResourceRun BinaryReflectedSerialRun BinaryFactoryHeight

structure Prepared (input : BinaryFourParameters.Input) (state : BinaryThreeResourceState.State)
    (K : ℕ) (outer : Fin K → Bool) extends BinaryReflectedPreparedDraw.Prepared input state K outer where
  factoryWork : ℕ

def prepareTerminal (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (N : ℕ) (bits : Fin N → Bool) (result : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) (K : ℕ) (outer : Fin K → Bool) : Prepared input result.state K outer :=
  let assembled := BinaryNestedTerminalPreparationWork.prepareWithWork (prepare input) result.state
  let factory := BinaryNestedSpecFactoryWork.profileWithWork assembled.1.1 K outer
  let table := BinaryTerminalProfileCompiler.permute factory.1 assembled.1.2
  have hTable : table = BinaryTerminalProfileCompiler.profile (prepare input) result.state K outer := by
    unfold table
    rw [BinaryNestedSpecFactoryWork.profileWithWork_state,BinaryNestedTerminalPreparationWork.prepareWithWork_state]
    rfl
  ⟨⟨table,(by rw [hTable]; exact BinaryTerminalProfileCompiler.profile_canonical _ result.state (prepare_canonical input hC) result.canonical K outer),
    (by rw [hTable]; exact profile_nonnegative input hC hAd N bits result hSuccess K outer),hTable,assembled.2⟩,factory.2⟩

theorem prepareTerminal_base (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (N : ℕ) (bits : Fin N → Bool) (result : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) (K : ℕ) (outer : Fin K → Bool) :
    (prepareTerminal input hC hAd N bits result hSuccess K outer).toPrepared =
      BinaryReflectedPreparedDraw.prepareTerminal input hC hAd N bits result hSuccess K outer := by
  unfold prepareTerminal BinaryReflectedPreparedDraw.prepareTerminal
  simp only [BinaryNestedSpecFactoryWork.profileWithWork_state]

theorem permute_height {n k : ℕ} (table : BinaryStoredOverlapEnvironment.Segment n k)
    (pi : Equiv.Perm (Fin n)) (s : ℕ) (h : SegmentHeight table s) :
    SegmentHeight (BinaryTerminalProfileCompiler.permute table pi) s := by
  refine ⟨h.1,?_⟩
  intro slot j
  simp only [BinaryTerminalProfileCompiler.permute,FixedArrayTable.read_ofFn]
  exact h.2 _ _

def bound (s K : ℕ) : ℕ := BinaryNestedSpecFactoryWork.bound (expressionHeightBudget s 23) K

theorem prepareTerminal_factoryWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (hAd : Admissible input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) (K : ℕ) (outer : Fin K → Bool) :
    (prepareTerminal input hC hAd N bits result hSuccess K outer).factoryWork ≤ bound s K := by
  have hHeight := BinaryNestedTerminalPreparationWork.reached_input_height input source hC hR hCase s hs hH N bits result hSuccess
  have hInputC : (BinaryNestedTerminalPreparationWork.prepareWithWork (prepare input) result.state).1.1.Canonical := by
    rw [BinaryNestedTerminalPreparationWork.prepareWithWork_state]
    exact BinaryNestedTerminalInput.prepare_canonical _ _ (prepare_canonical input hC) result.canonical
  have hs23 : 3 ≤ expressionHeightBudget s 23 := by unfold expressionHeightBudget; omega
  exact BinaryNestedSpecFactoryWork.profileWithWork_bound _ hInputC _ hs23 hHeight K outer

end Blotto.BinaryReflectedFactoryPrepared
