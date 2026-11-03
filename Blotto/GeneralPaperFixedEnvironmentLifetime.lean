import Blotto.GeneralPaperNativeSegmentCompilerLifetime

/-! Materialize the fixed environment once. Field reads/copies reserve their
written rational and scalar work record, while the array prefix and frames
stay live. The original cached fields and fixed code belong to borrowed. -/
namespace Blotto.GeneralPaperFixedEnvironmentLifetime
open GeneralPaperEncodedBasisStorage (arrayFootprint arrayProfile array_bound)
open GeneralPaperEncodedScalarStorage (natBits fields)
set_option autoImplicit false
set_option maxHeartbeats 1600000

def callback {k : ℕ} (A : ℕ) (values : Fin k → ℚ) (j : Fin k) : ℚ × ℕ :=
  (values j, rationalWordWidth (values j) + 32 * A + 32)

def copy {k : ℕ} (A : ℕ) (values : Fin k → ℚ) := PaperIndexedArrayConstruction.run id A (callback A values)

def stepFoot (A : ℕ) (q : ℚ) : ℕ :=
  let price := rationalWordWidth q + 32 * A + 32
  rationalWordWidth q + fields A [price, 32 * A, 32] + 64 * A

theorem step_bound (A s : ℕ) (q : ℚ) (h : RationalHeight q s) :
    stepFoot A q ≤ 512 * (1 + 2 * s + A + 1) := by
  let price := rationalWordWidth q + 32 * A + 32
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A price [price, 32 * A, 32] (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> dsimp only [price] <;> omega)
  change fields A [price, 32 * A, 32] ≤ 3 * (natBits price + A) + 32 * A at hFields
  have hBits : natBits price ≤ price + 2 := by
    have h := Nat.log2_le_self price
    change 1 + (price.log2 + 1) ≤ price + 2
    omega
  have hQ := rationalWordWidth_of_height h
  unfold stepFoot
  change rationalWordWidth q + fields A [price, 32 * A, 32] + 64 * A ≤ _
  dsimp only [price] at hFields hBits
  dsimp only [price]
  omega

def time (A k s : ℕ) : ℕ := k * (1 + 2 * s + 32 * A + 32) + PaperIndexedArrayConstruction.overhead id A k k

theorem work {k : ℕ} (A s : ℕ) (values : Fin k → ℚ) (h : ∀ j, RationalHeight (values j) s) :
    (copy A values).2 ≤ time A k s :=
  GeneralPaperPreparedSegmentCompaction.array_work k rfl A (1 + 2 * s + 32 * A + 32)
    (callback A values) (fun j => by have hw := rationalWordWidth_of_height (h j); unfold callback; dsimp only; omega)

inductive Phase (k : ℕ) where
  | active (j : Fin k)
  | returned

def window {k : ℕ} (A : ℕ) (values : Fin k → ℚ) (borrowed : ℕ) : Phase k → ℕ
  | .active j => GeneralPaperIndexedArrayLifetime.window id A (callback A values) rationalWordWidth j.val j.isLt.le
      borrowed (stepFoot A (values j))
  | .returned => borrowed + arrayFootprint A rationalWordWidth (copy A values).1 + fields A [(copy A values).2] + 64 * A

def profile (A k s borrowed : ℕ) : ℕ :=
  borrowed + arrayProfile A k (1 + 2 * s) +
    (k + 1) * GeneralPaperIndexedArrayLifetime.frame A k (time A k s) +
    512 * (1 + 2 * s + A + 1) + (natBits (time A k s) + A) + 96 * A

theorem all_phases {k : ℕ} (A s : ℕ) (values : Fin k → ℚ) (h : ∀ j, RationalHeight (values j) s)
    (borrowed : ℕ) (phase : Phase k) : window A values borrowed phase ≤ profile A k s borrowed := by
  have hWork := work A s values h
  cases phase with
  | active j =>
    have hWindow := GeneralPaperIndexedArrayLifetime.window_bound id A (callback A values) rationalWordWidth
      (1 + 2 * s) (512 * (1 + 2 * s + A + 1)) (fun i => rationalWordWidth_of_height (h i)) j.val j.isLt.le
      borrowed _ (step_bound A s (values j) (h j))
    have hFrame := GeneralPaperIndexedArrayLifetime.frame_mono A k _ _ hWork
    have hFrames := Nat.mul_le_mul_left (k + 1) hFrame
    change (k + 1) * GeneralPaperIndexedArrayLifetime.frame A k
      (PaperIndexedArrayConstruction.run id A (callback A values)).2 ≤ _ at hFrames
    simp only [window]
    unfold profile
    omega
  | returned =>
    have hPayload := array_bound A (1 + 2 * s) rationalWordWidth (copy A values).1 (by
      intro j
      rw [copy, PaperIndexedArrayConstruction.run_data, FixedArrayTable.read_ofFn]
      exact rationalWordWidth_of_height (h j))
    have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (time A k s) [(copy A values).2] (by
      intro x hx
      rw [List.mem_singleton.mp hx]
      exact hWork)
    simp only [List.length_singleton, one_mul] at hFields
    simp only [window]
    unfold profile
    omega

theorem pair_copy (B : ℚ) (A : ℕ) : copy A (fun _ : Fin 1 => B) = GeneralPaperPairSegmentPreparation.environment B A := rfl

theorem three_copy (i : RationalThreeSpec) (A : ℕ) :
    copy A (![i.B, i.a, i.d, i.c, i.p]) = GeneralPaperThreeSegmentPreparation.environment i A := rfl

end Blotto.GeneralPaperFixedEnvironmentLifetime
