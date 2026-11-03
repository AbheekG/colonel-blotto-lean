import Blotto.BinaryCachedFourParameterWork
import Blotto.BinaryReflectedFourSetup
import Blotto.RationalFourSmallHeight

/-! Actual reflected setup prepares the parameter table once, caches the
common initial scale once, then performs three short and three initial products.
It refines the original setup exactly. The following prices are primitive
arithmetic work; tables, indices, bookkeeping and physical ownership are separate. -/

namespace Blotto.BinaryReflectedSetupWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinaryReflectedFourSetup
open scoped BigOperators

def fromParametersWithWork (input : BinaryFourParameters.Input) (parameters : FixedArrayTable 8 SignedWord) : System × ℕ :=
  let lengths := originalLengths input
  let scale := applyWithWork .mul (parameters.read 6) (parameters.read 5)
  let shorts := FixedArrayTable.ofFn (fun j => applyWithWork .mul (parameters.read 4) (lengths.read j))
  let initial := FixedArrayTable.ofFn (fun j => applyWithWork .mul scale.1 (lengths.read j))
  (⟨parameters.read 7, lengths, FixedArrayTable.ofFn (fun j => (shorts.read j).1),
    FixedArrayTable.ofFn (fun j => (initial.read j).1)⟩,
    scale.2 + (∑ j : Fin 3, (shorts.read j).2) + (∑ j : Fin 3, (initial.read j).2))

theorem fromParametersWithWork_state (input : BinaryFourParameters.Input) (parameters : FixedArrayTable 8 SignedWord) :
    (fromParametersWithWork input parameters).1 = fromParameters input parameters := by
  unfold fromParametersWithWork fromParameters
  dsimp only
  simp only [FixedArrayTable.read_ofFn, applyWithWork_state]

theorem fromParametersWithWork_bound (input : BinaryFourParameters.Input) (parameters : FixedArrayTable 8 SignedWord)
    (hC : input.Canonical) (hP : ∀ j, CanonicalWord (parameters.read j)) (s : ℕ)
    (hParameters : ∀ j, RationalHeight (value (parameters.read j)) s)
    (hLengths : ∀ j, RationalHeight (value ((originalLengths input).read j)) s) :
    (fromParametersWithWork input parameters).2 ≤ 7 * (12000 * (2 + 4 * s) ^ 3) := by
  let Q := 12000 * (2 + 4 * s) ^ 3
  have hpWidth : ∀ j, width (parameters.read j) ≤ 1 + 4 * s := fun j =>
    (hP j).2.trans ((rationalWordWidth_of_height (hParameters j)).trans (by omega))
  have hlWidth : ∀ j, width ((originalLengths input).read j) ≤ 1 + 4 * s := fun j =>
    (originalLengths_canonical input hC j).2.trans ((rationalWordWidth_of_height (hLengths j)).trans (by omega))
  have hScale := BinaryPRGPreparationWork.operation_uniform_bound .mul (parameters.read 6) (parameters.read 5)
    (1 + 4 * s) (hpWidth 6) (hpWidth 5)
  have hScaleHeight : RationalHeight (value (applyWithWork .mul (parameters.read 6) (parameters.read 5)).1) (s + s) := by
    rw [applyWithWork_state, apply_value .mul _ _ (hP 6).1 (hP 5).1]
    exact (hParameters 6).mul (hParameters 5)
  have hScaleC := opcode_canonical .mul _ _ (hP 6) (hP 5)
  have hScaleWidth : width (applyWithWork .mul (parameters.read 6) (parameters.read 5)).1 ≤ 1 + 4 * s := by
    rw [applyWithWork_state]
    exact hScaleC.2.trans ((rationalWordWidth_of_height hScaleHeight).trans (by omega))
  have hShort : ∀ j, (applyWithWork .mul (parameters.read 4) ((originalLengths input).read j)).2 ≤ Q := by
    intro j
    have h := BinaryPRGPreparationWork.operation_uniform_bound .mul _ _ (1 + 4 * s) (hpWidth 4) (hlWidth j)
    simpa only [show 1 + 4 * s + 1 = 2 + 4 * s by omega] using h
  have hInitial : ∀ j, (applyWithWork .mul (applyWithWork .mul (parameters.read 6) (parameters.read 5)).1
      ((originalLengths input).read j)).2 ≤ Q := by
    intro j
    have h := BinaryPRGPreparationWork.operation_uniform_bound .mul _ _ (1 + 4 * s) hScaleWidth (hlWidth j)
    simpa only [show 1 + 4 * s + 1 = 2 + 4 * s by omega] using h
  have hShortSum : (∑ j : Fin 3, (applyWithWork .mul (parameters.read 4) ((originalLengths input).read j)).2) ≤ 3 * Q :=
    (Finset.sum_le_sum (fun j _ => hShort j)).trans_eq (by simp)
  have hInitialSum : (∑ j : Fin 3, (applyWithWork .mul (applyWithWork .mul (parameters.read 6) (parameters.read 5)).1
      ((originalLengths input).read j)).2) ≤ 3 * Q :=
    (Finset.sum_le_sum (fun j _ => hInitial j)).trans_eq (by simp)
  simp only [show 1 + 4 * s + 1 = 2 + 4 * s by omega] at hScale
  unfold fromParametersWithWork
  dsimp only
  simp only [FixedArrayTable.read_ofFn]
  dsimp only [Q] at hShortSum hInitialSum
  omega

def prepareWithWork (input : BinaryFourParameters.Input) : System × ℕ :=
  let parameters := BinaryFourParameters.prepareWithWork input
  let system := fromParametersWithWork input parameters.1
  (system.1, parameters.2 + system.2)

theorem prepareWithWork_state (input : BinaryFourParameters.Input) :
    (prepareWithWork input).1 = prepare input := by
  dsimp only [prepareWithWork, BinaryFourParameters.prepareWithWork, BinaryReflectedFourSetup.prepare]
  exact fromParametersWithWork_state input (BinaryFourParameters.prepare input)

def bound (s : ℕ) : ℕ := BinaryCachedFourParameterWork.parameterBound s +
  7 * (12000 * (2 + 4 * expressionHeightBudget s 12) ^ 3)

theorem prepareWithWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) :
    (prepareWithWork input).2 ≤ bound s := by
  have hP := BinaryFourParameters.prepareWork_bound input source hC hR s hs hH.environment
  have hParameters : ∀ j, RationalHeight (value ((BinaryFourParameters.prepare input).read j)) (expressionHeightBudget s 12) := by
    intro j
    rw [BinaryFourParameters.prepare_value input source hC hR j]
    exact hH.scalar hs j
  have hLengths : ∀ j, RationalHeight (value ((originalLengths input).read j)) (expressionHeightBudget s 12) := by
    intro j
    rw [originalLengths_value input source hR j]
    exact (hH.originalLengths j).mono (expressionHeightBudget_ge_input s 12)
  have hSystem := fromParametersWithWork_bound input (BinaryFourParameters.prepare input) hC
    (BinaryFourParameters.prepare_canonical input hC) _ hParameters hLengths
  exact Nat.add_le_add hP hSystem

def capacityWithWork (system : System) : FixedArrayTable 3 SignedWord × ℕ :=
  let subtractions := FixedArrayTable.ofFn (fun j => applyWithWork .sub (system.long.read j) (system.short.read j))
  (FixedArrayTable.ofFn (fun j => (subtractions.read j).1), ∑ j : Fin 3, (subtractions.read j).2)

theorem capacityWithWork_state (system : System) : (capacityWithWork system).1 = system.capacity := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  simp only [capacityWithWork, System.capacity, FixedArrayTable.read_ofFn, applyWithWork_state]

theorem capacityWithWork_bound (system : System) (hC : system.Canonical) (s : ℕ)
    (hLong : ∀ j, RationalHeight (value (system.long.read j)) s)
    (hShort : ∀ j, RationalHeight (value (system.short.read j)) s) :
    (capacityWithWork system).2 ≤ 3 * (12000 * (2 + 2 * s) ^ 3) := by
  have hEach : ∀ j, (applyWithWork .sub (system.long.read j) (system.short.read j)).2 ≤ 12000 * (2 + 2 * s) ^ 3 := by
    intro j
    have hp := BinaryPRGPreparationWork.operation_uniform_bound .sub _ _ (1 + 2 * s)
      ((hC.2.1 j).2.trans (rationalWordWidth_of_height (hLong j)))
      ((hC.2.2.1 j).2.trans (rationalWordWidth_of_height (hShort j)))
    simpa only [show 1 + 2 * s + 1 = 2 + 2 * s by omega] using hp
  unfold capacityWithWork
  dsimp only
  simp only [FixedArrayTable.read_ofFn]
  exact (Finset.sum_le_sum (fun j _ => hEach j)).trans_eq (by simp)

theorem actual_capacityWithWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) :
    (capacityWithWork (prepare input)).2 ≤ 3 * (12000 * (2 + 2 * expressionHeightBudget s 14) ^ 3) := by
  have hRef := prepare_refines input source hC hR hCase
  have hHeight := hH.reflectedResourceSystem hs hCase
  apply capacityWithWork_bound _ (prepare_canonical input hC)
  · intro j; rw [hRef.2.1 j]; exact hHeight.2.1 j
  · intro j; rw [hRef.2.2.1 j]; exact hHeight.2.2.1 j

end Blotto.BinaryReflectedSetupWork
