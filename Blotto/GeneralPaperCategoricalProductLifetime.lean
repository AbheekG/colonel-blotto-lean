import Blotto.GeneralPaperNaturalScalarLifetime

/-! Actual denominator-product recursion. Each activation counts the stored
probability, child product, scalar multiplication scratch, index and work
records. Pending parents are conservatively reserved across child calls. -/
namespace Blotto.GeneralPaperCategoricalProductLifetime
open GeneralPaperStoredCategoricalProduct (build)
open GeneralPaperEncodedScalarStorage (natBits fields)
set_option autoImplicit false
set_option maxHeartbeats 1800000

def localFoot {r : ℕ} (weights : FixedArrayTable r ℚ) (model : RationalCostModel) (A k : ℕ) (hk : k < r) : ℕ :=
  let child := build weights model A k hk.le
  let q := weights.read ⟨k, hk⟩
  let product := GeneralPaperNaturalScalarStep.run model A .mul child.1 q.den
  let actual := build weights model A (k + 1) hk
  rationalWordWidth q + GeneralPaperNaturalScalarLifetime.footprint model A .mul child.1 q.den +
    fields A [k, child.2, product.2, actual.2] + 128 * A

theorem local_bound {r : ℕ} (weights : FixedArrayTable r ℚ) (model : RationalCostModel) (A k : ℕ) (hk : k < r) :
    localFoot weights model A k hk ≤ 256 * (build weights model A (k + 1) hk).2 := by
  let child := build weights model A k hk.le
  let q := weights.read ⟨k, hk⟩
  let product := GeneralPaperNaturalScalarStep.run model A .mul child.1 q.den
  let F := (build weights model A (k + 1) hk).2
  have hF : F = child.2 + rationalWordWidth q + product.2 + 64 * (A + binaryWordWidth (k + 1) + 1) := rfl
  have hScratch := GeneralPaperNaturalScalarLifetime.bounded model A .mul child.1 q.den
  change GeneralPaperNaturalScalarLifetime.footprint model A .mul child.1 q.den ≤ 32 * product.2 at hScratch
  have hIndex : natBits k ≤ 1 + binaryWordWidth (k + 1) :=
    Nat.add_le_add_left (binaryWordWidth_mono (Nat.le_succ k)) 1
  have hWord (x : ℕ) (hx : x ≤ F) : natBits x ≤ F + 2 :=
    (GeneralPaperNaturalScalarLifetime.counter_word x).trans (by omega)
  have hFields := GeneralPaperEncodedScalarStorage.fields_bound A (F + 2) [k, child.2, product.2, F] (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · omega
    · exact hWord _ (by omega)
    · exact hWord _ (by omega)
    · exact hWord _ le_rfl)
  change fields A _ ≤ 4 * (F + 2 + A) + 32 * A at hFields
  change rationalWordWidth q + GeneralPaperNaturalScalarLifetime.footprint model A .mul child.1 q.den +
    fields A [k, child.2, product.2, F] + 128 * A ≤ 256 * F
  omega

def live {r : ℕ} (weights : FixedArrayTable r ℚ) (model : RationalCostModel) (A : ℕ) :
    (k : ℕ) → k ≤ r → ℕ
  | 0, _ => natBits 1 + fields A [64 * A + 64] + 64 * A
  | k + 1, hk => localFoot weights model A k hk + live weights model A k (by omega)

theorem bounded {r : ℕ} (weights : FixedArrayTable r ℚ) (model : RationalCostModel) (A k : ℕ) (hk : k ≤ r) :
    live weights model A k hk ≤ 256 * (k + 1) * (build weights model A k hk).2 := by
  induction k with
  | zero =>
    have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (64 * A + 64) [64 * A + 64]
      (by intro x hx; rw [List.mem_singleton.mp hx])
    have hBits : natBits (64 * A + 64) ≤ 64 * A + 66 := by
      have h := Nat.log2_le_self (64 * A + 64)
      unfold natBits binaryWordWidth
      omega
    have hOne : natBits 1 = 2 := by decide
    simp only [List.length_singleton, one_mul] at hFields
    simp only [live, build, Nat.zero_add, Nat.mul_one]
    rw [hOne]
    omega
  | succ k ih =>
    have hLocal := local_bound weights model A k hk
    have hChild := ih (by omega)
    have hMono : (build weights model A k (by omega)).2 ≤ (build weights model A (k + 1) hk).2 := by
      rw [build]
      dsimp only
      omega
    have hChildScale := hChild.trans (Nat.mul_le_mul_left (256 * (k + 1)) hMono)
    rw [live]
    nlinarith only [hLocal, hChildScale]

theorem native_height_bound {r s : ℕ} (weights : FixedArrayTable r ℚ) (model : RationalCostModel) (A k : ℕ)
    (hk : k ≤ r) (h : ∀ i, RationalHeight (weights.read i) s) :
    live weights model A k hk ≤ 256 * (r + 1) *
      (r * GeneralPaperStoredCategoricalProduct.stepBound model A r s + 64 * A + 64) :=
  (bounded weights model A k hk).trans (Nat.mul_le_mul (Nat.mul_le_mul_left 256 (Nat.add_le_add_right hk 1))
    ((GeneralPaperStoredCategoricalProduct.build_work weights model A k hk h).trans
      (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ hk) (64 * A)) 64)))

end Blotto.GeneralPaperCategoricalProductLifetime
