import Blotto.PreparedImplicitSampler
import Blotto.PreparedProductBatch

/-! Fixed independent seed blocks draw multiple whole rows from one stored
implicit sampler. The exact product-kernel identity and accumulated all-test
error are derived; no field independence or rebuilt guide is introduced. -/

namespace Blotto.ImplicitLeafCounts.PreparedImplicitSampler
open scoped Classical

abbrev Row (prepared : PreparedImplicitSampler) := Fin (prepared.tree.allocationTree prepared.nonnegative).fields → ℚ

def batch (prepared : PreparedImplicitSampler) (epsilon : ℚ) :
    (count : ℕ) → (Fin (count * prepared.bitBudget epsilon) → Bool) → List prepared.Row
  | 0, _ => []
  | count + 1, bits =>
      let width := prepared.bitBudget epsilon
      let seed : Fin (width + count * width) → Bool := fun j => bits (j.cast (by ring))
      prepared.drawRow epsilon (firstBitBlock width (count * width) seed) ::
        prepared.batch epsilon count (secondBitBlock width (count * width) seed)

theorem batch_length (prepared : PreparedImplicitSampler) (epsilon : ℚ) (count : ℕ)
    (bits : Fin (count * prepared.bitBudget epsilon) → Bool) : (prepared.batch epsilon count bits).length = count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [batch, List.length_cons, ih]

theorem batch_feasible (prepared : PreparedImplicitSampler) (epsilon : ℚ) (he : 0 < epsilon)
    (count : ℕ) (bits : Fin (count * prepared.bitBudget epsilon) → Bool) :
    ∀ row ∈ prepared.batch epsilon count bits, Feasible (prepared.budget : ℝ) (fun field => (row field : ℝ)) := by
  induction count with
  | zero => intro row h; simp [batch] at h
  | succ count ih =>
    intro row h
    simp only [batch, List.mem_cons] at h
    rcases h with rfl | h
    · exact (prepared.drawRow_contract epsilon he).1 _
    · exact ih _ row h

noncomputable def rowKernel (prepared : PreparedImplicitSampler) (actual : Bool) (epsilon : ℚ) :
    BoundedExpectationKernel prepared.Row :=
  if actual then (fairBitKernel (prepared.bitBudget epsilon)).map (prepared.drawRow epsilon)
  else (prepared.tree.projected.targetKernel prepared.budget
    (prepared.tree.prefix_positive_of_feasible_label prepared.budget prepared.fallback prepared.fallback_feasible)).map
      (fun label => prepared.tree.decodeLabel prepared.nonnegative (label.cast prepared.tree.projected.real_trueSize))

theorem rowKernel_close (prepared : PreparedImplicitSampler) (epsilon : ℚ) (he : 0 < epsilon) :
    (prepared.rowKernel true epsilon).Close (prepared.rowKernel false epsilon) (epsilon : ℝ) := by
  intro test hTest
  have h := (prepared.tree.epsilonOutput_contract prepared.certified prepared.budget
    (prepared.tree.prefix_positive_of_feasible_label prepared.budget prepared.fallback prepared.fallback_feasible)
    epsilon he prepared.fallback prepared.fallback_feasible).2
    (fun label => test (prepared.tree.decodeLabel prepared.nonnegative (label.cast prepared.tree.projected.real_trueSize)))
    (fun label => hTest _)
  exact h

noncomputable def batchKernel (prepared : PreparedImplicitSampler) (actual : Bool) (epsilon : ℚ) :
    ℕ → BoundedExpectationKernel (List prepared.Row)
  | 0 => BoundedExpectationKernel.point []
  | count + 1 => (prepared.rowKernel actual epsilon).bind
      (fun row => (prepared.batchKernel actual epsilon count).map (fun rows => row :: rows))

theorem batch_mean (prepared : PreparedImplicitSampler) (epsilon : ℚ) (count : ℕ)
    (test : List prepared.Row → ℝ) :
    (fairBitKernel (count * prepared.bitBudget epsilon)).mean (fun bits => test (prepared.batch epsilon count bits)) =
      (prepared.batchKernel true epsilon count).mean test := by
  induction count generalizing test with
  | zero => exact (fairBitKernel _).constant (test [])
  | succ count ih =>
    let width := prepared.bitBudget epsilon
    have hCast := fairBitKernel_cast (width + count * width) ((count + 1) * width) (by ring)
      (fun bits => test (prepared.batch epsilon (count + 1) bits))
    apply hCast.symm.trans
    have hBlocks := fairBitKernel_blocks width (count * width)
      (fun first rest => test (prepared.drawRow epsilon first :: prepared.batch epsilon count rest))
    apply hBlocks.trans
    apply congrArg (fairBitKernel width).mean
    funext first
    exact ih (fun rows => test (prepared.drawRow epsilon first :: rows))

theorem batchKernel_close (prepared : PreparedImplicitSampler) (epsilon : ℚ) (he : 0 < epsilon) (count : ℕ) :
    (prepared.batchKernel true epsilon count).Close (prepared.batchKernel false epsilon count)
      ((count : ℝ) * (epsilon : ℝ)) := by
  induction count with
  | zero => intro test _; simp only [batchKernel, BoundedExpectationKernel.point, sub_self, abs_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ count ih =>
    have hc := BoundedExpectationKernel.bind_close (prepared.rowKernel true epsilon) (prepared.rowKernel false epsilon)
      (fun row => (prepared.batchKernel true epsilon count).map (fun rows => row :: rows))
      (fun row => (prepared.batchKernel false epsilon count).map (fun rows => row :: rows))
      (epsilon : ℝ) ((count : ℝ) * (epsilon : ℝ)) (prepared.rowKernel_close epsilon he)
      (fun row => BoundedExpectationKernel.map_close _ _ (fun rows => row :: rows) _ ih)
    simp only [batchKernel]
    have hError : ((count + 1 : ℕ) : ℝ) * (epsilon : ℝ) = (epsilon : ℝ) + (count : ℝ) * (epsilon : ℝ) := by
      push_cast
      ring
    rw [hError]
    exact hc

theorem batch_mean_error (prepared : PreparedImplicitSampler) (epsilon : ℚ) (he : 0 < epsilon) (count : ℕ)
    (test : List prepared.Row → ℝ) (ht : ∀ rows, 0 ≤ test rows ∧ test rows ≤ 1) :
    |(fairBitKernel (count * prepared.bitBudget epsilon)).mean (fun bits => test (prepared.batch epsilon count bits)) -
      (prepared.batchKernel false epsilon count).mean test| ≤ (count : ℝ) * (epsilon : ℝ) := by
  rw [prepared.batch_mean]
  exact prepared.batchKernel_close epsilon he count test ht

def batchTolerance (accuracy : ℚ) (count : ℕ) : ℚ := accuracy / ((count : ℚ) + 1)

theorem batchTolerance_positive (accuracy : ℚ) (ha : 0 < accuracy) (count : ℕ) :
    0 < batchTolerance accuracy count := by unfold batchTolerance; positivity

theorem scheduled_batch_error (prepared : PreparedImplicitSampler) (accuracy : ℚ) (ha : 0 < accuracy) (count : ℕ)
    (test : List prepared.Row → ℝ) (ht : ∀ rows, 0 ≤ test rows ∧ test rows ≤ 1) :
    |(fairBitKernel (count * prepared.bitBudget (batchTolerance accuracy count))).mean
      (fun bits => test (prepared.batch (batchTolerance accuracy count) count bits)) -
      (prepared.batchKernel false (batchTolerance accuracy count) count).mean test| ≤ (accuracy : ℝ) := by
  have he := prepared.batch_mean_error (batchTolerance accuracy count) (batchTolerance_positive accuracy ha count) count test ht
  have hc : (0 : ℝ) ≤ count := by positivity
  have haR : (0 : ℝ) ≤ accuracy := by exact_mod_cast ha.le
  have hTol : (batchTolerance accuracy count : ℝ) = (accuracy : ℝ) / ((count : ℝ) + 1) := by simp [batchTolerance]
  rw [hTol] at he
  have hb : (count : ℝ) * ((accuracy : ℝ) / ((count : ℝ) + 1)) ≤ (accuracy : ℝ) := by
    calc
      _ = ((count : ℝ) * (accuracy : ℝ)) / ((count : ℝ) + 1) := by ring
      _ ≤ (accuracy : ℝ) := (div_le_iff₀ (by positivity : (0 : ℝ) < (count : ℝ) + 1)).mpr (by nlinarith)
  exact he.trans hb

end Blotto.ImplicitLeafCounts.PreparedImplicitSampler
