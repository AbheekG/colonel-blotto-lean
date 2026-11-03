import Blotto.PreparedRationalTransition
import Blotto.NativeAdaptiveBitHistory

/-! Actual raw rational training histories use fresh fixed-width fair blocks.
Unused suffix bits are ignored after a proved per-history width cap. Error is
accumulated before conditioning or postprocessing, and every generated row
retains its current prepared budget on every seed. -/

namespace Blotto
open scoped Classical

theorem fairBitKernel_prefix_mean (N B : ℕ) (h : N ≤ B) (test : (Fin N → Bool) → ℝ) :
    (fairBitKernel B).mean (fun bits => test (fun j => bits ⟨j.val, Nat.lt_of_lt_of_le j.isLt h⟩)) =
      (fairBitKernel N).mean test := by
  have hsize : B = N + (B - N) := by omega
  have hcast := fairBitKernel_cast (N + (B - N)) B hsize.symm
    (fun bits => test (fun j => bits ⟨j.val, Nat.lt_of_lt_of_le j.isLt h⟩))
  apply hcast.symm.trans
  have he := fairBitKernel_blocks N (B - N) (fun first _ => test first)
  have hprefix : (fun bits : Fin (N + (B - N)) → Bool =>
      test (fun j => bits ((⟨j.val, Nat.lt_of_lt_of_le j.isLt h⟩ : Fin B).cast hsize))) =
      fun bits => test (firstBitBlock N (B - N) bits) := by
    funext bits
    apply congrArg test
    funext j
    apply congrArg bits
    exact Fin.ext rfl
  rw [hprefix, he]
  simp only [(fairBitKernel (B - N)).constant]

namespace NativePreparedTrainingHistory

abbrev Observation (m : ℕ) := PreparedRationalTransition.Observation m

def sample {m : ℕ} (a b : List (Observation m) → PreparedProductSampler m)
    (values : RationalFieldSelector m) (epsilonA epsilonB : ℚ) (K B : ℕ)
    (history : List (Observation m)) (bits : Fin B → Bool) : Observation m :=
  if hWidth : PreparedProductTransition.bitBudget (a history) (b history) values epsilonA epsilonB K ≤ B then
    PreparedProductTransition.sample (a history) (b history) values epsilonA epsilonB K
      (fun j => bits ⟨j.val, Nat.lt_of_lt_of_le j.isLt hWidth⟩)
  else ((a history).tree.decode (a history).fallback ∘ (fun field => field.cast (a history).fields_eq.symm),
    (b history).tree.decode (b history).fallback ∘ (fun field => field.cast (b history).fields_eq.symm),
    values.attempt.fallbackLabel)

noncomputable def idealStep {m : ℕ} (a b : List (Observation m) → PreparedProductSampler m)
    (values : RationalFieldSelector m) (history : List (Observation m)) : BoundedExpectationKernel (Observation m) :=
  PreparedRationalTransition.idealKernel (a history) (b history) values

theorem step_close_before {m : ℕ} (a b : List (Observation m) → PreparedProductSampler m)
    (values : RationalFieldSelector m) (epsilonA epsilonB : ℚ) (hA : 0 < epsilonA) (hB : 0 < epsilonB) (K B L : ℕ)
    (hWidth : ∀ history, history.length < L →
      PreparedProductTransition.bitBudget (a history) (b history) values epsilonA epsilonB K ≤ B)
    (history : List (Observation m)) (hlen : history.length < L) :
    (bitHistoryStep B (sample a b values epsilonA epsilonB K B) history).Close
      (idealStep a b values history) ((epsilonA : ℝ) + (epsilonB : ℝ) + 1 / (2 : ℝ) ^ K) := by
  intro test htest
  have hFit := hWidth history hlen
  change |(fairBitKernel B).mean (fun bits => test (sample a b values epsilonA epsilonB K B history bits)) - _| ≤ _
  unfold sample
  simp only [hFit, dite_true]
  have hp := fairBitKernel_prefix_mean
    (PreparedProductTransition.bitBudget (a history) (b history) values epsilonA epsilonB K) B hFit
    (fun bits => test (PreparedProductTransition.sample (a history) (b history) values epsilonA epsilonB K bits))
  rw [hp]
  rw [PreparedRationalTransition.actualKernel_flat_mean]
  exact PreparedRationalTransition.kernel_close (a history) (b history) values epsilonA epsilonB hA hB K test htest

def run {m : ℕ} (a b : List (Observation m) → PreparedProductSampler m)
    (values : RationalFieldSelector m) (epsilonA epsilonB : ℚ) (K B : ℕ)
    (T : ℕ) (bits : Fin (T * B) → Bool) (history : List (Observation m)) : List (Observation m) :=
  runBitHistory B (sample a b values epsilonA epsilonB K B) T bits history

theorem run_bounded_error_before {m : ℕ} (a b : List (Observation m) → PreparedProductSampler m)
    (values : RationalFieldSelector m) (epsilonA epsilonB : ℚ) (hA : 0 < epsilonA) (hB : 0 < epsilonB) (K B L : ℕ)
    (hWidth : ∀ history, history.length < L →
      PreparedProductTransition.bitBudget (a history) (b history) values epsilonA epsilonB K ≤ B)
    (T : ℕ) (history : List (Observation m)) (hLimit : T + history.length ≤ L)
    (test : List (Observation m) → ℝ) (htest : ∀ history, 0 ≤ test history ∧ test history ≤ 1) :
    |(fairBitKernel (T * B)).mean (fun bits => test (run a b values epsilonA epsilonB K B T bits history)) -
      (BoundedExpectationKernel.historyRun (idealStep a b values) T history).mean test| ≤
        (T : ℝ) * ((epsilonA : ℝ) + (epsilonB : ℝ) + 1 / (2 : ℝ) ^ K) := by
  exact runBitHistory_bounded_error_before B _ _ _
    (by have hAR : (0 : ℝ) ≤ (epsilonA : ℝ) := by exact_mod_cast hA.le
        have hBR : (0 : ℝ) ≤ (epsilonB : ℝ) := by exact_mod_cast hB.le
        positivity)
    L (step_close_before a b values epsilonA epsilonB hA hB K B L hWidth) T history hLimit test htest

theorem run_event_error_before {m : ℕ} (a b : List (Observation m) → PreparedProductSampler m)
    (values : RationalFieldSelector m) (epsilonA epsilonB : ℚ) (hA : 0 < epsilonA) (hB : 0 < epsilonB) (K B L : ℕ)
    (hWidth : ∀ history, history.length < L →
      PreparedProductTransition.bitBudget (a history) (b history) values epsilonA epsilonB K ≤ B)
    (T : ℕ) (history : List (Observation m)) (hLimit : T + history.length ≤ L)
    (event : Set (List (Observation m))) :
    |(fairBitKernel (T * B)).mean (fun bits => if run a b values epsilonA epsilonB K B T bits history ∈ event then 1 else 0) -
      (BoundedExpectationKernel.historyRun (idealStep a b values) T history).mean
        (fun past => if past ∈ event then 1 else 0)| ≤
        (T : ℝ) * ((epsilonA : ℝ) + (epsilonB : ℝ) + 1 / (2 : ℝ) ^ K) :=
  run_bounded_error_before a b values epsilonA epsilonB hA hB K B L hWidth T history hLimit
    (fun past => if past ∈ event then 1 else 0)
    (fun past => by split_ifs <;> norm_num)

theorem fallback_feasible {m : ℕ} (prepared : PreparedProductSampler m) :
    Feasible (prepared.budget : ℝ)
      (fun field => (prepared.tree.decode prepared.fallback (field.cast prepared.fields_eq.symm) : ℝ)) := by
  have h := prepared.tree.realRow_feasible prepared.fallback prepared.budget prepared.fallback_feasible
  constructor
  · intro field
    exact h.1 (field.cast prepared.fields_eq.symm)
  · have he := Equiv.sum_comp (ProductArrayTree.finCastEquiv prepared.fields_eq.symm)
      (fun field => (prepared.tree.decode prepared.fallback field : ℝ))
    exact he.trans_le h.2

theorem sample_feasible {m : ℕ} (a b : List (Observation m) → PreparedProductSampler m)
    (values : RationalFieldSelector m) (epsilonA epsilonB : ℚ) (K B : ℕ)
    (history : List (Observation m)) (bits : Fin B → Bool) :
    Feasible ((a history).budget : ℝ) (fun field => ((sample a b values epsilonA epsilonB K B history bits).1 field : ℝ)) ∧
      Feasible ((b history).budget : ℝ) (fun field => ((sample a b values epsilonA epsilonB K B history bits).2.1 field : ℝ)) := by
  unfold sample
  split
  · exact PreparedProductTransition.sample_feasible _ _ _ _ _ _ _
  · exact ⟨fallback_feasible (a history), fallback_feasible (b history)⟩

theorem run_feasible {m : ℕ} (a b : List (Observation m) → PreparedProductSampler m)
    (values : RationalFieldSelector m) (epsilonA epsilonB : ℚ) (K B : ℕ)
    (budgetA budgetB : ℚ) (hA : ∀ history, (a history).budget = budgetA)
    (hB : ∀ history, (b history).budget = budgetB) (T : ℕ)
    (bits : Fin (T * B) → Bool) (history : List (Observation m))
    (hInitial : ∀ observation ∈ history,
      Feasible (budgetA : ℝ) (fun field => (observation.1 field : ℝ)) ∧
        Feasible (budgetB : ℝ) (fun field => (observation.2.1 field : ℝ))) :
    ∀ observation ∈ run a b values epsilonA epsilonB K B T bits history,
      Feasible (budgetA : ℝ) (fun field => (observation.1 field : ℝ)) ∧
        Feasible (budgetB : ℝ) (fun field => (observation.2.1 field : ℝ)) := by
  induction T generalizing history with
  | zero => exact hInitial
  | succ T ih =>
    unfold run runBitHistory
    apply ih
    intro observation hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · have he := sample_feasible a b values epsilonA epsilonB K B history
        (firstBitBlock B (T * B) (fun j => bits (j.cast (by ring))))
      rw [hA, hB] at he
      exact he
    · exact hInitial observation hmem

end NativePreparedTrainingHistory
end Blotto
