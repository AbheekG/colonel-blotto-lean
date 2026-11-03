import Blotto.PreparedProductSampler
import Blotto.FairBitKernelBlocks

/-! Multiple whole rows reuse one prepared tree. Flat fair-bit addresses give
fixed disjoint row blocks. The two-player expectation factors through separate
blocks, retaining dependence among coordinates of each sampled allocation. -/

namespace Blotto
open scoped BigOperators
namespace PreparedProductSampler

theorem rowBlockAddress {N B : ℕ} (i : Fin N) (j : Fin B) : i.val * B + j.val < N * B := by
  calc
    _ < i.val * B + B := Nat.add_lt_add_left j.isLt _
    _ = (i.val + 1) * B := by ring
    _ ≤ N * B := Nat.mul_le_mul_right B (Nat.succ_le_of_lt i.isLt)

def rowBlock {N B : ℕ} (bits : Fin (N * B) → Bool) (row : Fin N) : Fin B → Bool :=
  fun j => bits ⟨row.val * B + j.val, rowBlockAddress row j⟩

def batch {m : ℕ} (prepared : PreparedProductSampler m) (epsilon : ℚ) (N : ℕ)
    (bits : Fin (N * prepared.bitBudget epsilon) → Bool) : Fin N → Fin m → ℚ :=
  fun row => prepared.sample epsilon (rowBlock bits row)

theorem batch_feasible {m : ℕ} (prepared : PreparedProductSampler m) (epsilon : ℚ) (N : ℕ)
    (bits : Fin (N * prepared.bitBudget epsilon) → Bool) (row : Fin N) :
    Feasible (prepared.budget : ℝ) (fun field => (prepared.batch epsilon N bits row field : ℝ)) :=
  prepared.sample_feasible epsilon (rowBlock bits row)

def pairSample {m : ℕ} (a b : PreparedProductSampler m) (epsilonA epsilonB : ℚ)
    (bits : Fin (a.bitBudget epsilonA + b.bitBudget epsilonB) → Bool) : (Fin m → ℚ) × (Fin m → ℚ) :=
  (a.sample epsilonA (firstBitBlock (a.bitBudget epsilonA) (b.bitBudget epsilonB) bits),
   b.sample epsilonB (secondBitBlock (a.bitBudget epsilonA) (b.bitBudget epsilonB) bits))

theorem pairSample_feasible {m : ℕ} (a b : PreparedProductSampler m) (epsilonA epsilonB : ℚ)
    (bits : Fin (a.bitBudget epsilonA + b.bitBudget epsilonB) → Bool) :
    Feasible (a.budget : ℝ) (fun field => ((pairSample a b epsilonA epsilonB bits).1 field : ℝ)) ∧
      Feasible (b.budget : ℝ) (fun field => ((pairSample a b epsilonA epsilonB bits).2 field : ℝ)) :=
  ⟨a.sample_feasible epsilonA _, b.sample_feasible epsilonB _⟩

theorem pairSample_independent_mean {m : ℕ} (a b : PreparedProductSampler m) (epsilonA epsilonB : ℚ)
    (test : (Fin m → ℚ) → (Fin m → ℚ) → ℝ) :
    (fairBitKernel (a.bitBudget epsilonA + b.bitBudget epsilonB)).mean
      (fun bits => test (pairSample a b epsilonA epsilonB bits).1 (pairSample a b epsilonA epsilonB bits).2) =
    (fairBitKernel (a.bitBudget epsilonA)).mean (fun bitsA =>
      (fairBitKernel (b.bitBudget epsilonB)).mean (fun bitsB =>
        test (a.sample epsilonA bitsA) (b.sample epsilonB bitsB))) :=
  fairBitKernel_blocks _ _ (fun bitsA bitsB => test (a.sample epsilonA bitsA) (b.sample epsilonB bitsB))

end PreparedProductSampler
end Blotto
