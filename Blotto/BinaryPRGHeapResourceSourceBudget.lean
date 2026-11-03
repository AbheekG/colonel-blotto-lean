import Blotto.BinaryPRGHeapResourceMaterialization
import Blotto.BinaryPRGHeapResourceLoopBudget

/-! Compose the physical array preparation envelope with the recursive loop's
invariant-indexed step budget. The source invariant and numerical step price
remain explicit inputs until they are derived from original word widths. -/

namespace Blotto.BinaryPRGHeapResourceSourceBudget
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGWordControllerWordStore (lookup)
open BinaryPRGHeapResourceLoop (Finished)

variable {n : ℕ}

theorem runWithRetainedCap_bound (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (Inv : Finished (BinaryPRGHeapResourceSource.capStore capacity) n
      (BinaryPRGHeapResourceSource.count capacity) → Prop) (M : ℕ)
    (budget : BinaryPRGHeapResourceLoopBudget.ReachableStepBudget seed
      (BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR).1.1
      (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
      Inv M)
    (hInv : Inv (BinaryPRGHeapResourceSource.initialWithWork
      capacity resource hC hR).1.2) :
    (BinaryPRGHeapResourceSource.runWithRetainedCap
      seed capacity resource hC hR).2 ≤
      BinaryPRGHeapResourceSource.initialWorkEnvelope capacity resource +
      n * (2 * M) + 5 := by
  let prepared := BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR
  have hInitial := BinaryPRGHeapResourceSource.initialWithWork_bound
    capacity resource hC hR
  change prepared.2 ≤
    BinaryPRGHeapResourceSource.initialWorkEnvelope capacity resource at hInitial
  have hLoop := BinaryPRGHeapResourceLoopBudget.runWithWork_inputCount_bound
    seed prepared.1.1
    (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
    Inv M budget prepared.1.2 hInv
    (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _)
  unfold BinaryPRGHeapResourceSource.runWithRetainedCap
  dsimp only
  change prepared.2 +
    (BinaryPRGHeapResourceLoop.runWithWork seed prepared.1.1
      (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
      prepared.1.2 (BinaryWordIndexCoinController.zeroIndex seed)
      (by rw [BinaryWordIndexCoinController.zeroIndex_value]; exact Nat.zero_le _)).2 + 3 ≤
    BinaryPRGHeapResourceSource.initialWorkEnvelope capacity resource +
      n * (2 * M) + 5
  omega

theorem runNativeWithWork_some_bound (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (Inv : Finished (BinaryPRGHeapResourceSource.capStore capacity) n
      (BinaryPRGHeapResourceSource.count capacity) → Prop) (M : ℕ)
    (budget : BinaryPRGHeapResourceLoopBudget.ReachableStepBudget seed
      (BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR).1.1
      (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
      Inv M)
    (hInv : Inv (BinaryPRGHeapResourceSource.initialWithWork
      capacity resource hC hR).1.2)
    (state : Finished (BinaryPRGHeapResourceSource.capStore capacity) n
      (BinaryPRGHeapResourceSource.count capacity))
    (hSome : (BinaryPRGHeapResourceSource.runWithRetainedCap
      seed capacity resource hC hR).1.2.1 = some state) :
    (BinaryPRGHeapResourceMaterialization.runNativeWithWork
      seed capacity resource hC hR).2 ≤
      BinaryPRGHeapResourceSource.initialWorkEnvelope capacity resource +
      n * (2 * M) +
      BinaryPRGHeapResourceMaterialization.terminalUniformBound
        (BinaryPRGHeapResourceSource.runWithRetainedCap
          seed capacity resource hC hR).1.1 state + 9 := by
  have hSource := runWithRetainedCap_bound seed capacity resource hC hR Inv M budget hInv
  have hNative := BinaryPRGHeapResourceMaterialization.runNativeWithWork_some_bound
    seed capacity resource hC hR state hSome
  omega

theorem runNativeWithWork_none_bound (seed : BinarySeedLookupTree.Store)
    (capacity resource : FixedArrayTable n SignedWord)
    (hC : ∀ j,CanonicalWord (capacity.read j))
    (hR : ∀ j,CanonicalWord (resource.read j))
    (Inv : Finished (BinaryPRGHeapResourceSource.capStore capacity) n
      (BinaryPRGHeapResourceSource.count capacity) → Prop) (M : ℕ)
    (budget : BinaryPRGHeapResourceLoopBudget.ReachableStepBudget seed
      (BinaryPRGHeapResourceSource.initialWithWork capacity resource hC hR).1.1
      (BinaryPRGWordControllerBooleanResourceSource.capacityCanonical capacity hC)
      Inv M)
    (hInv : Inv (BinaryPRGHeapResourceSource.initialWithWork
      capacity resource hC hR).1.2)
    (hNone : (BinaryPRGHeapResourceSource.runWithRetainedCap
      seed capacity resource hC hR).1.2.1 = none) :
    (BinaryPRGHeapResourceMaterialization.runNativeWithWork
      seed capacity resource hC hR).2 ≤
      BinaryPRGHeapResourceSource.initialWorkEnvelope capacity resource +
      n * (2 * M) + 7 := by
  have hSource := runWithRetainedCap_bound seed capacity resource hC hR Inv M budget hInv
  have hNative := BinaryPRGHeapResourceMaterialization.runNativeWithWork_none_bound
    seed capacity resource hC hR hNone
  omega

end Blotto.BinaryPRGHeapResourceSourceBudget
