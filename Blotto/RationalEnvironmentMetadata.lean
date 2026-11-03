import Blotto.RationalArrayConstructionWork
import Blotto.IndexedLoopMetadataWork
import Blotto.RationalExpressionValue

/-! Environment materialization prices full-prefix rational payload copying
and index/capacity loop metadata. Formula evaluation and input production are
separate; no physical pointer/allocator/ownership claim is made. -/

namespace Blotto

def rationalEnvironmentMetadataWork {k : ℕ} (primitive : ℕ → ℕ) (env : FixedArrayTable k ℚ) : ℕ :=
  rationalArrayCopyWork (List.ofFn env.read) 0 + indexedLoopMetadataBitWork primitive 0 k

def rationalEnvironmentMetadataBound (c k W : ℕ) : ℕ :=
  2 * k * (k * W) + indexedLoopMetadataBound c k

theorem rationalEnvironmentMetadataBound_mono (c : ℕ) {k K W V : ℕ} (hk : k ≤ K) (hW : W ≤ V) :
    rationalEnvironmentMetadataBound c k W ≤ rationalEnvironmentMetadataBound c K V := by
  have hLoop := indexedLoopMetadataBound_mono c hk
  unfold rationalEnvironmentMetadataBound
  gcongr

theorem rationalEnvironmentMetadataWork_bound {k : ℕ} (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (env : FixedArrayTable k ℚ) (W : ℕ)
    (hEnv : ∀ j, rationalWordWidth (env.read j) ≤ W) :
    rationalEnvironmentMetadataWork primitive env ≤ rationalEnvironmentMetadataBound c k W := by
  have hCopy := rationalArrayCopyWork_bound (List.ofFn env.read) 0
  have hWords := rationalWordWidth_sum_bound (List.ofFn env.read) W
    (by intro q hq; rcases List.mem_ofFn.mp hq with ⟨j, rfl⟩; exact hEnv j)
  simp only [List.length_ofFn, Nat.zero_add] at hCopy hWords
  have hPayload := hCopy.trans (Nat.mul_le_mul_left (2 * k) hWords)
  have hLoop := indexedLoopMetadataBitWork_bound primitive c hPrimitive k
  unfold rationalEnvironmentMetadataWork rationalEnvironmentMetadataBound
  omega

end Blotto
