import Blotto.BinaryReflectedSetupWork
import Blotto.BinaryNestedTerminalPreparationWork

/-! A native reflected setup retains its actual parameter array, system and
one computed capacity table. Their exact original-data equalities and primitive
prefix price follow the original six words. No supplied factory is consumed;
metadata/ownership/physical allocation remain separate. -/

namespace Blotto.BinaryReflectedSetupCache
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedFourSetup

structure Prepared (input : BinaryFourParameters.Input) where
  parameters : FixedArrayTable 8 SignedWord
  parameters_correct : parameters = BinaryFourParameters.prepare input
  parameters_canonical : ∀ j, CanonicalWord (parameters.read j)
  system : System
  system_correct : system = prepare input
  canonical : system.Canonical
  capacity : FixedArrayTable 3 SignedWord
  capacity_correct : capacity = system.capacity
  capacity_canonical : ∀ j, CanonicalWord (capacity.read j)
  prefixWork : ℕ

def prepareCache (input : BinaryFourParameters.Input) (hC : input.Canonical) : Prepared input :=
  let parameters := BinaryFourParameters.prepareWithWork input
  let system := BinaryReflectedSetupWork.fromParametersWithWork input parameters.1
  let capacity := BinaryReflectedSetupWork.capacityWithWork system.1
  have hParameters : parameters.1 = BinaryFourParameters.prepare input := rfl
  have hSystem : system.1 = prepare input := by
    rw [BinaryReflectedSetupWork.fromParametersWithWork_state,hParameters]
    rfl
  have hCanonical : system.1.Canonical := by rw [hSystem]; exact prepare_canonical input hC
  have hCapacity := BinaryReflectedSetupWork.capacityWithWork_state system.1
  ⟨parameters.1,hParameters,(by rw [hParameters]; exact BinaryFourParameters.prepare_canonical input hC),
    system.1,hSystem,hCanonical,capacity.1,hCapacity,
    (by rw [hCapacity]; exact capacity_canonical system.1 hCanonical),parameters.2 + system.2 + capacity.2⟩

def bound (s : ℕ) : ℕ := BinaryReflectedSetupWork.bound s + 3 * (12000 * (2 + 2 * expressionHeightBudget s 14) ^ 3)

theorem prepareCache_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) : (prepareCache input hC).prefixWork ≤ bound s := by
  have hSetup := BinaryReflectedSetupWork.prepareWithWork_bound input source hC hR s hs hH
  have hCapacity := BinaryReflectedSetupWork.actual_capacityWithWork_bound input source hC hR hCase s hs hH
  change (BinaryReflectedSetupWork.prepareWithWork input).2 +
    (BinaryReflectedSetupWork.capacityWithWork (BinaryReflectedSetupWork.prepareWithWork input).1).2 ≤ _
  rw [BinaryReflectedSetupWork.prepareWithWork_state]
  exact Nat.add_le_add hSetup hCapacity

theorem Prepared.system_height (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) (prepared : Prepared input) :
    BinaryNestedTerminalPreparationWork.SystemHeight prepared.system (expressionHeightBudget s 14) := by
  rw [prepared.system_correct]
  have hr := prepare_refines input source hC hR hCase
  have hh := hH.reflectedResourceSystem hs hCase
  refine ⟨?_,?_,?_⟩
  · rw [hr.1]; exact hh.1
  · intro j; rw [hr.2.1 j]; exact hh.2.1 j
  · intro j; rw [hr.2.2.1 j]; exact hh.2.2.1 j

end Blotto.BinaryReflectedSetupCache
