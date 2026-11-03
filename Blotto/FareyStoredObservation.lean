import Blotto.FareyStoredBlockPreparation
import Blotto.ExactPreparedTrainingHistory

/-! A whole-player label is drawn once, then its complete rational row is
materialized into a sized array. Retained observations contain only row tables
and the selected field, rather than closures capturing guides or seed tapes.
All paths, including width overflow, refine the existing prepared observation.
Coordinate decoding and conservative array copying still require full prices. -/

namespace Blotto.FareyImplicitTrainer
open Farey ImplicitLeafCounts ProductSecurityTrainer

structure StoredObservation (m : ℕ) where
  first : FixedArrayTable m ℚ
  second : FixedArrayTable m ℚ
  field : Fin m

namespace StoredObservation

def reference {m : ℕ} (observed : StoredObservation m) : RawObservation m :=
  (observed.first.read, observed.second.read, observed.field)

end StoredObservation

namespace NativeBlockState

def directPreparedA {n : ℕ} {input : DirectInput (n + 1)} (state : NativeBlockState input) : PreparedAccessSampler :=
  PreparedAccessSampler.prepareZero (leafComb n state.firstLeaf) (leafCombAccess n state.firstLeaf state.firstAccess)
    (leafComb_nonnegative n state.firstLeaf state.firstLeaf_nonnegative) (leafComb_zero n state.firstLeaf state.firstLeaf_zero)
    input.budgetA input.budgetA_nonnegative

def directPreparedB {n : ℕ} {input : DirectInput (n + 1)} (state : NativeBlockState input) : PreparedAccessSampler :=
  PreparedAccessSampler.prepareZero (leafComb n state.secondLeaf) (leafCombAccess n state.secondLeaf state.secondAccess)
    (leafComb_nonnegative n state.secondLeaf state.secondLeaf_nonnegative) (leafComb_zero n state.secondLeaf state.secondLeaf_zero)
    input.budgetB input.budgetB_nonnegative

theorem directPreparedA_fields {n : ℕ} {input : DirectInput (n + 1)} (state : NativeBlockState input) :
    (state.directPreparedA.model.tree.allocationTree state.directPreparedA.model.nonnegative).fields = n + 1 := by
  unfold directPreparedA
  rw [PreparedAccessSampler.prepareZero_model_eq]
  exact ((leafComb n state.firstLeaf).rebuild_allocation_fields (leafComb_nonnegative n state.firstLeaf state.firstLeaf_nonnegative)
    (leafComb n state.firstLeaf).constructionGamma (leafComb n state.firstLeaf).constructionGamma_ge_one).trans
    (leafComb_fields n state.firstLeaf state.firstLeaf_nonnegative)

theorem directPreparedB_fields {n : ℕ} {input : DirectInput (n + 1)} (state : NativeBlockState input) :
    (state.directPreparedB.model.tree.allocationTree state.directPreparedB.model.nonnegative).fields = n + 1 := by
  unfold directPreparedB
  rw [PreparedAccessSampler.prepareZero_model_eq]
  exact ((leafComb n state.secondLeaf).rebuild_allocation_fields (leafComb_nonnegative n state.secondLeaf state.secondLeaf_nonnegative)
    (leafComb n state.secondLeaf).constructionGamma (leafComb n state.secondLeaf).constructionGamma_ge_one).trans
    (leafComb_fields n state.secondLeaf state.secondLeaf_nonnegative)

theorem directPreparedA_sized {n : ℕ} {input : DirectInput (n + 1)} (state : NativeBlockState input) :
    state.directPreparedA.sized state.directPreparedA_fields = state.preparedA := rfl

theorem directPreparedB_sized {n : ℕ} {input : DirectInput (n + 1)} (state : NativeBlockState input) :
    state.directPreparedB.sized state.directPreparedB_fields = state.preparedB := rfl

end NativeBlockState

namespace PreparedAccessSampler

def materialize {m : ℕ} (prepared : PreparedAccessSampler)
    (fields : (prepared.model.tree.allocationTree prepared.model.nonnegative).fields = m) (epsilon : ℚ)
    (bits : Fin (prepared.bitBudget epsilon) → Bool) : FixedArrayTable m ℚ :=
  let label := prepared.drawLabel epsilon bits
  FixedArrayTable.ofFn (fun field => prepared.model.tree.decodeLabel prepared.model.nonnegative label (field.cast fields.symm))

theorem materialize_read {m : ℕ} (prepared : PreparedAccessSampler)
    (fields : (prepared.model.tree.allocationTree prepared.model.nonnegative).fields = m) (epsilon : ℚ)
    (bits : Fin (prepared.bitBudget epsilon) → Bool) :
    (materialize prepared fields epsilon bits).read = (prepared.sized fields).draw epsilon bits := by
  funext field
  exact FixedArrayTable.read_ofFn _ field

def materializeFallback {m : ℕ} (prepared : PreparedAccessSampler)
    (fields : (prepared.model.tree.allocationTree prepared.model.nonnegative).fields = m) : FixedArrayTable m ℚ :=
  let label := prepared.model.fallback
  FixedArrayTable.ofFn (fun field => prepared.model.tree.decodeLabel prepared.model.nonnegative label (field.cast fields.symm))

theorem materializeFallback_read {m : ℕ} (prepared : PreparedAccessSampler)
    (fields : (prepared.model.tree.allocationTree prepared.model.nonnegative).fields = m) :
    (materializeFallback prepared fields).read = NativeImplicitTrainingHistory.fallbackRow (prepared.sized fields).model := by
  funext field
  exact FixedArrayTable.read_ofFn _ field

end PreparedAccessSampler

namespace StoredObservation

def sample {m : ℕ} (first second : PreparedAccessSampler)
    (fieldsFirst : (first.model.tree.allocationTree first.model.nonnegative).fields = m)
    (fieldsSecond : (second.model.tree.allocationTree second.model.nonnegative).fields = m)
    (values : RationalFieldSelector m) (epsilonA epsilonB : ℚ) (K B : ℕ) (bits : Fin B → Bool) : StoredObservation m :=
  let firstDraw := first.sized fieldsFirst
  let secondDraw := second.sized fieldsSecond
  if hWidth : ExactSizedTrainingTransition.bitBudget firstDraw secondDraw values epsilonA epsilonB K ≤ B then
    let seed : Fin (first.bitBudget epsilonA + (second.bitBudget epsilonB + values.attempt.bitBudget K)) → Bool :=
      fun j => bits ⟨j.val, Nat.lt_of_lt_of_le j.isLt (by change first.bitBudget epsilonA + second.bitBudget epsilonB + values.attempt.bitBudget K ≤ B at hWidth; omega)⟩
    let firstBits := firstBitBlock (first.bitBudget epsilonA) (second.bitBudget epsilonB + values.attempt.bitBudget K) seed
    let rest := secondBitBlock (first.bitBudget epsilonA) (second.bitBudget epsilonB + values.attempt.bitBudget K) seed
    { first := PreparedAccessSampler.materialize first fieldsFirst epsilonA firstBits
      second := PreparedAccessSampler.materialize second fieldsSecond epsilonB
        (firstBitBlock (second.bitBudget epsilonB) (values.attempt.bitBudget K) rest)
      field := PreparedProductTransition.fieldSample values K
        (secondBitBlock (second.bitBudget epsilonB) (values.attempt.bitBudget K) rest) }
  else
    { first := PreparedAccessSampler.materializeFallback first fieldsFirst
      second := PreparedAccessSampler.materializeFallback second fieldsSecond
      field := values.attempt.fallbackLabel }

theorem sample_reference {m : ℕ} (first second : PreparedAccessSampler)
    (fieldsFirst : (first.model.tree.allocationTree first.model.nonnegative).fields = m)
    (fieldsSecond : (second.model.tree.allocationTree second.model.nonnegative).fields = m)
    (values : RationalFieldSelector m) (epsilonA epsilonB : ℚ) (K B : ℕ) (bits : Fin B → Bool) :
    (sample first second fieldsFirst fieldsSecond values epsilonA epsilonB K B bits).reference =
      ExactPreparedTrainingHistory.preparedSample (first.sized fieldsFirst) (second.sized fieldsSecond) values epsilonA epsilonB K B bits := by
  by_cases hw : ExactSizedTrainingTransition.bitBudget (first.sized fieldsFirst) (second.sized fieldsSecond) values epsilonA epsilonB K ≤ B
  · unfold sample ExactPreparedTrainingHistory.preparedSample
    dsimp only
    rw [dite_eq_left hw, dite_eq_left hw]
    unfold reference ExactSizedTrainingTransition.sample
    dsimp only
    rw [PreparedAccessSampler.materialize_read, PreparedAccessSampler.materialize_read]
    rfl
  · unfold sample ExactPreparedTrainingHistory.preparedSample
    dsimp only
    rw [dite_eq_right hw, dite_eq_right hw]
    unfold reference
    dsimp only
    rw [PreparedAccessSampler.materializeFallback_read, PreparedAccessSampler.materializeFallback_read]

end StoredObservation

namespace NativeBlockState

def storedSample {n : ℕ} {input : DirectInput (n + 1)} (state : NativeBlockState input)
    (epsilonA epsilonB : ℚ) (K B : ℕ) (bits : Fin B → Bool) : StoredObservation (n + 1) :=
  let first := state.directPreparedA
  let second := state.directPreparedB
  StoredObservation.sample first second state.directPreparedA_fields state.directPreparedB_fields input.values epsilonA epsilonB K B bits

theorem storedSample_reference {n : ℕ} {input : DirectInput (n + 1)} (state : NativeBlockState input)
    (epsilonA epsilonB : ℚ) (K B : ℕ) (bits : Fin B → Bool) :
    (state.storedSample epsilonA epsilonB K B bits).reference =
      ExactPreparedTrainingHistory.preparedSample state.preparedA state.preparedB input.values epsilonA epsilonB K B bits := by
  rw [storedSample, StoredObservation.sample_reference, state.directPreparedA_sized, state.directPreparedB_sized]

theorem storedSample_feasible {n : ℕ} {input : DirectInput (n + 1)} (state : NativeBlockState input)
    (epsilonA epsilonB : ℚ) (hA : 0 < epsilonA) (hB : 0 < epsilonB) (K B : ℕ) (bits : Fin B → Bool) :
    Feasible (input.budgetA : ℝ) (fun field => ((state.storedSample epsilonA epsilonB K B bits).first.read field : ℝ)) ∧
      Feasible (input.budgetB : ℝ) (fun field => ((state.storedSample epsilonA epsilonB K B bits).second.read field : ℝ)) := by
  have h := ExactSizedTrainingHistory.sample_feasible (fun _ => state.preparedA) (fun _ => state.preparedB) input.values
    epsilonA epsilonB hA hB K B [] bits
  change Feasible (state.preparedA.budget : ℝ)
    (fun field => ((ExactPreparedTrainingHistory.preparedSample state.preparedA state.preparedB input.values epsilonA epsilonB K B bits).1 field : ℝ)) ∧
    Feasible (state.preparedB.budget : ℝ)
    (fun field => ((ExactPreparedTrainingHistory.preparedSample state.preparedA state.preparedB input.values epsilonA epsilonB K B bits).2.1 field : ℝ)) at h
  rw [← state.storedSample_reference, state.preparedA_budget, state.preparedB_budget] at h
  exact h

end NativeBlockState
end Blotto.FareyImplicitTrainer
