import Blotto.PreparedImplicitPair

/-! Stored implicit samplers expose rational whole rows at the original field
count. The size equality is proof-erased; all runtime draws use stored guides.
Their target law and hard budget transfer through the coordinate bijection. -/

namespace Blotto.ImplicitLeafCounts
open scoped BigOperators Classical

structure SizedImplicitSampler (m : ℕ) where
  stored : PreparedImplicitSampler
  fields : (stored.tree.allocationTree stored.nonnegative).fields = m

namespace SizedImplicitSampler

def bitBudget {m : ℕ} (prepared : SizedImplicitSampler m) (epsilon : ℚ) : ℕ := prepared.stored.bitBudget epsilon
def budget {m : ℕ} (prepared : SizedImplicitSampler m) : ℚ := prepared.stored.budget

def reindex {m : ℕ} (prepared : SizedImplicitSampler m) (row : prepared.stored.Row) : Fin m → ℚ :=
  fun field => row (field.cast prepared.fields.symm)

def sample {m : ℕ} (prepared : SizedImplicitSampler m) (epsilon : ℚ)
    (bits : Fin (prepared.bitBudget epsilon) → Bool) : Fin m → ℚ := prepared.reindex (prepared.stored.drawRow epsilon bits)

theorem sample_feasible {m : ℕ} (prepared : SizedImplicitSampler m) (epsilon : ℚ) (he : 0 < epsilon)
    (bits : Fin (prepared.bitBudget epsilon) → Bool) :
    Feasible (prepared.budget : ℝ) (fun field => (prepared.sample epsilon bits field : ℝ)) := by
  have h := (prepared.stored.drawRow_contract epsilon he).1 bits
  constructor
  · intro field
    exact h.1 (field.cast prepared.fields.symm)
  · change (∑ field : Fin m, (prepared.stored.drawRow epsilon bits (field.cast prepared.fields.symm) : ℝ)) ≤ _
    have hSum := Equiv.sum_comp (finCongr prepared.fields.symm)
      (fun field => (prepared.stored.drawRow epsilon bits field : ℝ))
    exact (le_of_eq hSum).trans h.2

noncomputable def nativeKernel {m : ℕ} (prepared : SizedImplicitSampler m) (epsilon : ℚ) :
    BoundedExpectationKernel (Fin m → ℚ) := (fairBitKernel (prepared.bitBudget epsilon)).map (prepared.sample epsilon)

noncomputable def targetKernel {m : ℕ} (prepared : SizedImplicitSampler m) :
    BoundedExpectationKernel (Fin m → ℚ) := (prepared.stored.rowKernel false 1).map prepared.reindex

theorem nativeKernel_close {m : ℕ} (prepared : SizedImplicitSampler m) (epsilon : ℚ) (he : 0 < epsilon) :
    (prepared.nativeKernel epsilon).Close prepared.targetKernel (epsilon : ℝ) := by
  have h := BoundedExpectationKernel.map_close (prepared.stored.rowKernel true epsilon)
    (prepared.stored.rowKernel false epsilon) prepared.reindex (epsilon : ℝ) (prepared.stored.rowKernel_close epsilon he)
  exact h

end SizedImplicitSampler
end Blotto.ImplicitLeafCounts
