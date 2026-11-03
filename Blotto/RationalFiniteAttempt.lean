import Blotto.RationalCategoricalLaw
import Blotto.FiniteRejectionCost

/-! Existing cached Boolean rational-coin execution realizes one finite
rational attempt from a bounded fair-bit block. The error holds for every
output event after a total decoder; zero-weight labels remain total paths. -/

namespace Blotto
open MeasureTheory Set
open scoped BigOperators Classical

structure RationalFiniteAttempt (labels outputs : ℕ) where
  weight : Fin labels → ℚ
  nonnegative : ∀ i, 0 ≤ weight i
  sum_one : ∑ i, weight i = 1
  decode : Fin labels → Option (Fin outputs)
  fallbackLabel : Fin labels

namespace RationalFiniteAttempt

def bitBudget {r n : ℕ} (_a : RationalFiniteAttempt r n) (K : ℕ) : ℕ := 3 * (r - 1 + K)

def sampleLabel {r n : ℕ} (a : RationalFiniteAttempt r n) (K : ℕ)
    (bits : Fin (a.bitBudget K) → Bool) : Fin r :=
  (categoricalMachine a.fallbackLabel).output (a.bitBudget K)
    (.remaining (rationalWeightList a.weight a.nonnegative)) a.fallbackLabel bits

def sample {r n : ℕ} (a : RationalFiniteAttempt r n) (K : ℕ)
    (bits : Fin (a.bitBudget K) → Bool) : Option (Fin n) := a.decode (a.sampleLabel K bits)

noncomputable def realAttempt {r n : ℕ} (a : RationalFiniteAttempt r n) : FiniteRejectionAttempt r n where
  probability := fun i => (a.weight i : ℝ)
  result := a.decode
  nonnegative := by intro i; exact_mod_cast a.nonnegative i
  sum_one := by exact_mod_cast a.sum_one

noncomputable def eventProbability {r n : ℕ} (a : RationalFiniteAttempt r n) (K : ℕ)
    (event : Set (Option (Fin n))) : ℝ :=
  ((fairBitLaw (a.bitBudget K) : Measure (Fin (a.bitBudget K) → Bool)).real
    {bits | a.sample K bits ∈ event})

noncomputable def idealEventProbability {r n : ℕ} (a : RationalFiniteAttempt r n)
    (event : Set (Option (Fin n))) : ℝ :=
  ∑ i, (a.weight i : ℝ) * (if a.decode i ∈ event then 1 else 0)

theorem sampleLabel_eq {r n : ℕ} (a : RationalFiniteAttempt r n) (K : ℕ)
    (bits : Fin (a.bitBudget K) → Bool) :
    a.sampleLabel K bits = (categoricalMachine a.fallbackLabel).output (3 * (r - 1 + K))
      (.remaining (rationalWeightList a.weight a.nonnegative)) a.fallbackLabel bits := rfl

theorem sample_invariant {r n : ℕ} (a : RationalFiniteAttempt r n) (predicate : Option (Fin n) → Prop)
    (h : ∀ i, predicate (a.decode i)) (K : ℕ) (bits : Fin (a.bitBudget K) → Bool) :
    predicate (a.sample K bits) := h _

theorem sample_failure_is_allowed {r n : ℕ} (a : RationalFiniteAttempt r n) (K : ℕ)
    (bits : Fin (a.bitBudget K) → Bool) : ∃ i, a.sample K bits = a.decode i :=
  ⟨a.sampleLabel K bits, rfl⟩

theorem eventProbability_error {r n : ℕ} (a : RationalFiniteAttempt r n) (K : ℕ)
    (event : Set (Option (Fin n))) :
    |a.eventProbability K event - a.idealEventProbability event| ≤ 1 / (2 : ℝ) ^ K := by
  have he := rationalCategorical_capped_event a.weight a.nonnegative a.sum_one a.fallbackLabel K
    {i | a.decode i ∈ event}
  unfold eventProbability idealEventProbability sample sampleLabel bitBudget
  unfold WordStateMachine.cappedLaw at he
  rw [ProbabilityMeasure.toMeasure_map, Measure.real, Measure.map_apply_of_aemeasurable (measurable_of_countable _).aemeasurable
    (Set.toFinite {i : Fin r | a.decode i ∈ event}).measurableSet] at he
  exact he

theorem outputMass_error {r n : ℕ} (a : RationalFiniteAttempt r n) (K : ℕ) (x : Fin n) :
    |a.eventProbability K {some x} - a.realAttempt.outputMass x| ≤ 1 / (2 : ℝ) ^ K := by
  have he := a.eventProbability_error K {some x}
  have hIdeal : a.idealEventProbability {some x} = a.realAttempt.outputMass x := by
    unfold idealEventProbability realAttempt FiniteRejectionAttempt.outputMass
    apply Finset.sum_congr rfl
    intro i _
    simp only [mem_singleton_iff]
    split_ifs <;> simp
  rw [hIdeal] at he
  exact he

theorem failureMass_error {r n : ℕ} (a : RationalFiniteAttempt r n) (K : ℕ) :
    |a.eventProbability K {none} - a.realAttempt.failureMass| ≤ 1 / (2 : ℝ) ^ K := by
  have he := a.eventProbability_error K {none}
  have hIdeal : a.idealEventProbability {none} = a.realAttempt.failureMass := by
    unfold idealEventProbability realAttempt FiniteRejectionAttempt.failureMass
    apply Finset.sum_congr rfl
    intro i _
    simp only [mem_singleton_iff]
    split_ifs <;> simp
  rw [hIdeal] at he
  exact he

theorem sample_consumed_bits_le {r n : ℕ} (a : RationalFiniteAttempt r n) (K : ℕ)
    (bits : Fin (a.bitBudget K) → Bool) :
    ((categoricalMachine a.fallbackLabel).run (a.bitBudget K)
      (.remaining (rationalWeightList a.weight a.nonnegative)) bits).2 ≤ a.bitBudget K :=
  (categoricalMachine a.fallbackLabel).run_bits_le _ _ bits

theorem bitBudget_bound {r n : ℕ} (a : RationalFiniteAttempt r n) (K : ℕ) :
    a.bitBudget K ≤ 3 * (r + K) := by unfold bitBudget; omega

end RationalFiniteAttempt
end Blotto
