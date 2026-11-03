import Blotto.BinaryReflectedCategoricalWork
import Blotto.BinaryStoredSegmentDrawWork

/-! Selected reflected emission consumes an already prepared terminal table:
one midpoint/interpolation row, three native subtractions, and the original zero
coordinate. Actual reached source heights derive all prices and exact bytes.
Profile construction, metadata/ownership and compiler costs remain separate. -/

namespace Blotto.BinaryReflectedSelectedEmissionWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode BinaryReflectedFourSetup
open BinarySharedResourceRun BinaryReflectedPhaseRefinement
open scoped BigOperators

def reflectWithWork (input : BinaryFourParameters.Input) (row : FixedArrayTable 3 SignedWord) : FixedArrayTable 4 SignedWord × ℕ :=
  let lengths := originalLengths input
  let returned := FixedArrayTable.ofFn (fun j => applyWithWork .sub (lengths.read j) (row.read j))
  (FixedArrayTable.ofFn ![(returned.read 0).1,(returned.read 1).1,(returned.read 2).1,zero],
    ∑ j : Fin 3, (returned.read j).2)

theorem reflectWithWork_state (input : BinaryFourParameters.Input) (row : FixedArrayTable 3 SignedWord) :
    (reflectWithWork input row).1 = reflect input row := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  fin_cases j <;> simp only [reflectWithWork,reflect,originalLengths,FixedArrayTable.read_ofFn,applyWithWork_state] <;> rfl

theorem reflectWithWork_bound (input : BinaryFourParameters.Input) (row : FixedArrayTable 3 SignedWord)
    (hC : input.Canonical) (hRow : ∀ j, CanonicalWord (row.read j)) (s : ℕ)
    (hLengths : ∀ j, RationalHeight (value ((originalLengths input).read j)) s)
    (hHeight : ∀ j, RationalHeight (value (row.read j)) s) :
    (reflectWithWork input row).2 ≤ 36000 * (2 + 2 * s) ^ 3 := by
  have hEach : ∀ j, (applyWithWork .sub ((originalLengths input).read j) (row.read j)).2 ≤ 12000 * (2 + 2 * s) ^ 3 := by
    intro j
    have h := BinaryPRGPreparationWork.operation_uniform_bound .sub _ _ (1 + 2 * s)
      ((originalLengths_canonical input hC j).2.trans (rationalWordWidth_of_height (hLengths j)))
      ((hRow j).2.trans (rationalWordWidth_of_height (hHeight j)))
    simpa only [show 1 + 2 * s + 1 = 2 + 2 * s by omega] using h
  unfold reflectWithWork
  simp only [FixedArrayTable.read_ofFn]
  exact (Finset.sum_le_sum (fun j _ => hEach j)).trans_eq (by simp; ring)

def sampleWithWork (input : BinaryFourParameters.Input) (table : BinaryStoredOverlapEnvironment.Segment 3 18)
    (slot : Fin 18) (K : ℕ) (scalar : Fin K → Bool) : FixedArrayTable 4 SignedWord × ℕ :=
  let row := BinarySegmentPoint.sampleWithWork table slot K scalar
  let returned := reflectWithWork input row.1
  (returned.1,row.2 + returned.2)

theorem sampleWithWork_state (input : BinaryFourParameters.Input) (table : BinaryStoredOverlapEnvironment.Segment 3 18)
    (slot : Fin 18) (K : ℕ) (scalar : Fin K → Bool) :
    (sampleWithWork input table slot K scalar).1 = reflect input (BinarySegmentPoint.sample table slot K scalar) := by
  unfold sampleWithWork
  rw [reflectWithWork_state,BinarySegmentPoint.sampleWithWork_state]

def bound (s K : ℕ) : ℕ :=
  BinaryStoredSegmentDrawWork.pointBound 3 (expressionHeightBudget (max s (K + 2)) 68) K +
    36000 * (2 + 2 * expressionHeightBudget (max s (K + 2)) 71) ^ 3

theorem reached_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (N : ℕ) (bits : Fin N → Bool)
    (result : BinaryThreeResourcePair.Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) (K : ℕ) (outer scalar : Fin K → Bool) (slot : Fin 18) :
    (sampleWithWork input (BinaryTerminalProfileCompiler.profile (prepare input) result.state K outer) slot K scalar).2 ≤ bound s K := by
  let table := BinaryTerminalProfileCompiler.profile (prepare input) result.state K outer
  let terminal := (source.reflectedResourceSystem hCase).terminalData (phaseResult input source hC hR hCase N bits result hSuccess)
  let W := max s (K + 2)
  have hTable := BinaryTerminalProfileCompiler.profile_canonical _ result.state (prepare_canonical input hC) result.canonical K outer
  have hRef := terminal_profile_refines input source hC hR hCase N bits result hSuccess K outer
  have hHeight := BinaryReflectedReachedHeight.profile_height input source hC hR hCase s hs hH N bits result hSuccess K outer
  have hs68 : 2 ≤ expressionHeightBudget W 68 := hs.trans ((le_max_left s (K + 2)).trans (expressionHeightBudget_ge_input W 68))
  have hPointWork := BinarySegmentPoint.sampleWork_bound table (terminal.profile K outer) hTable hRef
    (expressionHeightBudget W 68) hs68 hHeight.2 slot K scalar
  have hPrecision : K + 2 ≤ expressionHeightBudget W 68 := (le_max_right s (K + 2)).trans (expressionHeightBudget_ge_input W 68)
  have hRow := BinarySegmentPoint.sample_canonical table slot K scalar hTable
  have hRowHeight : ∀ j, RationalHeight (value ((BinarySegmentPoint.sample table slot K scalar).read j)) (expressionHeightBudget W 71) := by
    intro j
    rw [BinarySegmentPoint.sample_value table (terminal.profile K outer) hTable hRef]
    have h := hHeight.point hs68 K slot scalar j
    rw [max_eq_left hPrecision,expressionHeightBudget_comp] at h
    exact h
  have hLengths : ∀ j, RationalHeight (value ((originalLengths input).read j)) (expressionHeightBudget W 71) := by
    intro j
    rw [originalLengths_value input source hR j]
    exact (hH.originalLengths j).mono ((le_max_left s (K + 2)).trans (expressionHeightBudget_ge_input W 71))
  have hReflect := reflectWithWork_bound input (BinarySegmentPoint.sample table slot K scalar) hC hRow
    _ hLengths hRowHeight
  exact Nat.add_le_add hPointWork hReflect

end Blotto.BinaryReflectedSelectedEmissionWork
