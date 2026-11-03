import Blotto.BinaryScalarTape
import Blotto.BinaryPRGHeapTerminalLifetime
import Blotto.BinaryPRGGlobalFallbackLifetime

/-! Complete physical PRG optional resource/cache/terminal execution joins its
original global B-zero fallback, selected only on exhaustion. Every exact native
row and absolute cursor is preserved; no local fixed four fallback is used. -/
namespace Blotto.BinaryPRGHeapFixedLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryPRGResourceWork
set_option maxHeartbeats 2000000

def runWithTrace {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) : (FixedArrayTable n SignedWord × FixedBinaryWord store.width) × Trace :=
  let drawn := BinaryPRGHeapTerminalLifetime.runWithTrace store request rich K outer scalar
  match drawn.1.1 with
  | some row => ((row,drawn.1.2),wrap 24 2 [drawn.2])
  | none =>
      let fallback := BinaryPRGGlobalFallbackLifetime.prepareWithTrace (resourceInput request rich)
      ((fallback.1,drawn.1.2),wrap 32 2 [drawn.2,fallback.2])

theorem runWithTrace_erasure {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (runWithTrace store request rich K outer scalar).1 =
      (BinaryPRGWordControllerRequest.fixedSample store request rich K outer scalar,
        (BinaryPRGWordControllerRequest.run store request rich K outer scalar).2) := by
  unfold runWithTrace BinaryPRGWordControllerRequest.fixedSample
  dsimp only
  rw [← BinaryPRGHeapTerminalLifetime.runWithTrace_erasure store request rich K outer scalar]
  cases (BinaryPRGHeapTerminalLifetime.runWithTrace store request rich K outer scalar).1.1 with
  | some row => rfl
  | none => exact Prod.ext (BinaryPRGGlobalFallbackLifetime.prepareWithTrace_erasure _) rfl

theorem runWithTrace_state {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (runWithTrace store request rich K outer scalar).1.1 =
      (BinaryPRGCachedPrimitiveRun.fixedSample request rich K store.cap.value outer scalar
        (BinaryWordIndexCoinController.reader store)).1 := by
  rw [runWithTrace_erasure]
  exact BinaryPRGWordControllerRequest.fixedSample_state store request rich K outer scalar

theorem runWithTrace_cursor {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (runWithTrace store request rich K outer scalar).1.2 =
      (BinaryPRGWordControllerRequest.run store request rich K outer scalar).2 := by
  rw [runWithTrace_erasure]

theorem runWithTrace_position {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (runWithTrace store request rich K outer scalar).1.2.value ≤ store.cap.value := by
  rw [runWithTrace_cursor]
  exact BinaryPRGWordControllerRequest.run_position store request rich K outer scalar

noncomputable def envelope {n : ℕ} (request : BinaryPRGRequest.Request n) (K i b : ℕ) : ℕ :=
  BinaryPRGHeapTerminalLifetime.envelope request K i b+BinaryPRGGlobalFallbackLifetime.envelope n+128

theorem runWithTrace_usage {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    usage (runWithTrace store request rich K outer scalar).2 ≤ envelope request K store.width store.cap.value := by
  let drawn := BinaryPRGHeapTerminalLifetime.runWithTrace store request rich K outer scalar
  have hD := BinaryPRGHeapTerminalLifetime.runWithTrace_usage store request rich K outer scalar
  have hF := BinaryPRGGlobalFallbackLifetime.prepareWithTrace_usage (resourceInput request rich)
  change usage drawn.2 ≤ _ at hD
  unfold runWithTrace
  dsimp only
  split
  · have hw := wrap_usage 24 2 [drawn.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 24 2 [drawn.2]) ≤ _
    unfold envelope
    omega
  · have hw := wrap_usage 32 2 [drawn.2,
      (BinaryPRGGlobalFallbackLifetime.prepareWithTrace (resourceInput request rich)).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 32 2 [drawn.2,
      (BinaryPRGGlobalFallbackLifetime.prepareWithTrace (resourceInput request rich)).2]) ≤ _
    unfold envelope
    omega

theorem all_prefix {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace store request rich K outer scalar).2 steps ≤
      borrowed+envelope request K store.width store.cap.value ∧
      framePeak ((runWithTrace store request rich K outer scalar).2.take steps) ≤ envelope request K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _ (runWithTrace_usage store request rich K outer scalar) borrowed steps

theorem runWithTrace_canonical {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    ∀ j,CanonicalWord ((runWithTrace store request rich K outer scalar).1.1.read j) := by
  rw [runWithTrace_erasure]
  exact BinaryPRGWordControllerRequest.fixedSample_canonical store request rich K outer scalar

theorem runWithTrace_fullBudget {n : ℕ} (store : BinarySeedLookupTree.Store) (request : BinaryPRGRequest.Request n) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    FullBudget (value (resourceInput request rich).budget : ℝ)
      (fun j => (value ((runWithTrace store request rich K outer scalar).1.1.read j) : ℝ)) := by
  rw [runWithTrace_erasure]
  exact BinaryPRGWordControllerRequest.fixedSample_fullBudget store request rich K outer scalar

end Blotto.BinaryPRGHeapFixedLifetime
