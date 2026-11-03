import Blotto.BinaryTerminalPhysicalDrawLifetime
import Blotto.BinaryPRGHeapFixedLifetime

/-! Accepted physical terminal execution with the original global exhaustion
fallback. The normalized row and absolute cursor are preserved exactly. -/
namespace Blotto.BinaryTerminalPhysicalFixedLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryPRGResourceWork
set_option maxHeartbeats 2000000

private abbrev PhysicalParsed :=
  (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool

def runWithTrace (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (FixedArrayTable parsed.1.1 SignedWord × FixedBinaryWord store.width) × Trace :=
  let request := parsed.1.2.logical.request
  let drawn := BinaryTerminalPhysicalDrawLifetime.runWithTrace
    frame parsed hParsed store rich K outer scalar
  match drawn.1.1 with
  | some row => ((row,drawn.1.2),wrap 24 2 [drawn.2])
  | none =>
      let fallback := BinaryPRGGlobalFallbackLifetime.prepareWithTrace
        (resourceInput request rich)
      ((fallback.1,drawn.1.2),wrap 32 2 [drawn.2,fallback.2])

theorem accepted_erasure (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (runWithTrace frame parsed hParsed store rich K outer scalar).1 =
      (BinaryPRGWordControllerRequest.fixedSample store
        parsed.1.2.logical.request rich K outer scalar,
        (BinaryPRGWordControllerRequest.run store
          parsed.1.2.logical.request rich K outer scalar).2) := by
  unfold runWithTrace BinaryPRGWordControllerRequest.fixedSample
  dsimp only
  rw [← BinaryTerminalPhysicalDrawLifetime.accepted_erasure
    frame parsed hParsed store rich K outer scalar]
  cases (BinaryTerminalPhysicalDrawLifetime.runWithTrace
      frame parsed hParsed store rich K outer scalar).1.1 with
  | some row => rfl
  | none => exact Prod.ext (BinaryPRGGlobalFallbackLifetime.prepareWithTrace_erasure _) rfl

theorem accepted_logical_output (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (runWithTrace frame parsed hParsed store rich K outer scalar).1 =
      (BinaryPRGHeapFixedLifetime.runWithTrace store
        parsed.1.2.logical.request rich K outer scalar).1 := by
  rw [accepted_erasure,BinaryPRGHeapFixedLifetime.runWithTrace_erasure]

theorem accepted_state (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (runWithTrace frame parsed hParsed store rich K outer scalar).1.1 =
      (BinaryPRGCachedPrimitiveRun.fixedSample parsed.1.2.logical.request rich K
        store.cap.value outer scalar (BinaryWordIndexCoinController.reader store)).1 := by
  rw [accepted_erasure]
  exact BinaryPRGWordControllerRequest.fixedSample_state store
    parsed.1.2.logical.request rich K outer scalar

theorem accepted_cursor (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (runWithTrace frame parsed hParsed store rich K outer scalar).1.2 =
      (BinaryPRGWordControllerRequest.run store
        parsed.1.2.logical.request rich K outer scalar).2 := by
  rw [accepted_erasure]

theorem accepted_position (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (runWithTrace frame parsed hParsed store rich K outer scalar).1.2.value ≤
      store.cap.value := by
  rw [accepted_cursor]
  exact BinaryPRGWordControllerRequest.run_position store
    parsed.1.2.logical.request rich K outer scalar

theorem accepted_canonical (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    ∀ j, CanonicalWord
      ((runWithTrace frame parsed hParsed store rich K outer scalar).1.1.read j) := by
  rw [accepted_erasure]
  exact BinaryPRGWordControllerRequest.fixedSample_canonical store
    parsed.1.2.logical.request rich K outer scalar

theorem accepted_fullBudget (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    FullBudget (value (resourceInput parsed.1.2.logical.request rich).budget : ℝ)
      (fun j => (value ((runWithTrace frame parsed hParsed store rich K outer scalar).1.1.read j) : ℝ)) := by
  rw [accepted_erasure]
  exact BinaryPRGWordControllerRequest.fixedSample_fullBudget store
    parsed.1.2.logical.request rich K outer scalar

noncomputable def envelope (frame : List Bool)
    (parsed : Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n)
    (store : BinarySeedLookupTree.Store) (K : ℕ) : ℕ :=
  BinaryTerminalPhysicalDrawLifetime.envelope frame parsed store K+
    BinaryPRGGlobalFallbackLifetime.envelope parsed.1+128

theorem accepted_usage_additive (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    usage (runWithTrace frame parsed hParsed store rich K outer scalar).2 ≤
      usage (BinaryTerminalPhysicalDrawLifetime.runWithTrace
        frame parsed hParsed store rich K outer scalar).2+
        BinaryPRGGlobalFallbackLifetime.envelope parsed.1.1+128 := by
  let request := parsed.1.2.logical.request
  let drawn := BinaryTerminalPhysicalDrawLifetime.runWithTrace
    frame parsed hParsed store rich K outer scalar
  have hF := BinaryPRGGlobalFallbackLifetime.prepareWithTrace_usage
    (resourceInput request rich)
  unfold runWithTrace
  dsimp only
  split
  · have hw := wrap_usage 24 2 [drawn.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 24 2 [drawn.2]) ≤
      usage drawn.2+BinaryPRGGlobalFallbackLifetime.envelope parsed.1.1+128
    omega
  · have hw := wrap_usage 32 2 [drawn.2,
      (BinaryPRGGlobalFallbackLifetime.prepareWithTrace
        (resourceInput request rich)).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 32 2 [drawn.2,
      (BinaryPRGGlobalFallbackLifetime.prepareWithTrace
        (resourceInput request rich)).2]) ≤
      usage drawn.2+BinaryPRGGlobalFallbackLifetime.envelope parsed.1.1+128
    omega

theorem accepted_usage (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    usage (runWithTrace frame parsed hParsed store rich K outer scalar).2 ≤
      envelope frame parsed.1 store K := by
  have hAdd := accepted_usage_additive frame parsed hParsed store rich K outer scalar
  have hDraw := BinaryTerminalPhysicalDrawLifetime.accepted_usage
    frame parsed hParsed store rich K outer scalar
  unfold envelope
  omega

theorem accepted_uniform_polynomial :
    ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : PhysicalParsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (store : BinarySeedLookupTree.Store) (rich : Bool)
      (K : ℕ) (outer scalar : BinaryScalarTape K),
      usage (runWithTrace frame parsed hParsed store rich K outer scalar).2 ≤
        C*(frame.length+K+store.width+store.cap.value+3)^d := by
  obtain ⟨C₁,d₁,hDraw⟩ :=
    BinaryTerminalPhysicalDrawLifetime.accepted_uniform_polynomial
  obtain ⟨C₂,d₂,hCont⟩ :=
    BinaryPRGFullOutputLifetimePolynomial.continuation_polynomial
  refine ⟨C₁+C₂*5^d₂+128,max d₁ d₂,?_⟩
  intro frame parsed hParsed store rich K outer scalar
  let s := parsed.1.2.logical.request.source.originalInputWordWidth
  let X := frame.length+K+store.width+store.cap.value+3
  let D := max d₁ d₂
  have hX : 0 < X := by dsimp only [X]; omega
  have hn := BinaryTerminalPhysicalRouteLifetime.accepted_dimension
    frame parsed hParsed
  have hs := BinaryTerminalPhysicalRouteLifetime.accepted_source_width
    frame parsed hParsed
  have hDrawBound := hDraw frame parsed hParsed store rich K outer scalar
  change usage (BinaryTerminalPhysicalDrawLifetime.runWithTrace
      frame parsed hParsed store rich K outer scalar).2 ≤ C₁*X^d₁ at hDrawBound
  have hContBound := hCont
    ⟨parsed.1.1,s,K,store.width,store.cap.value,0⟩
  change BinaryPRGFullOutputLifetimePolynomial.continuationEnvelope
      parsed.1.1 s K store.width store.cap.value 0 ≤
        C₂*(parsed.1.1+s+K+store.width+store.cap.value+1)^d₂ at hContBound
  have hFallbackBase : BinaryPRGGlobalFallbackLifetime.envelope parsed.1.1 ≤
      BinaryPRGFullOutputLifetimePolynomial.continuationEnvelope
        parsed.1.1 s K store.width store.cap.value 0 := by
    dsimp only [BinaryPRGFullOutputLifetimePolynomial.continuationEnvelope]
    omega
  have hSize : parsed.1.1+s+K+store.width+store.cap.value+1 ≤ 5*X := by
    dsimp only [s,X] at *
    omega
  have hFallbackTop : BinaryPRGGlobalFallbackLifetime.envelope parsed.1.1 ≤
      C₂*5^d₂*X^d₂ := by
    have hp := Nat.mul_le_mul_left C₂ (Nat.pow_le_pow_left hSize d₂)
    rw [Nat.mul_pow] at hp
    exact (hFallbackBase.trans hContBound).trans (hp.trans_eq (by ring))
  have hAdd := accepted_usage_additive frame parsed hParsed store rich K outer scalar
  have h₁ : X^d₁ ≤ X^D :=
    Nat.pow_le_pow_right hX (Nat.le_max_left d₁ d₂)
  have h₂ : X^d₂ ≤ X^D :=
    Nat.pow_le_pow_right hX (Nat.le_max_right d₁ d₂)
  have hOne : 1 ≤ X^D := Nat.one_le_pow D X (by omega)
  have hScale₁ := Nat.mul_le_mul_left C₁ h₁
  have hScale₂ := Nat.mul_le_mul_left (C₂*5^d₂) h₂
  change usage (runWithTrace frame parsed hParsed store rich K outer scalar).2 ≤
    (C₁+C₂*5^d₂+128)*X^D
  calc
    _ ≤ usage (BinaryTerminalPhysicalDrawLifetime.runWithTrace
          frame parsed hParsed store rich K outer scalar).2+
        BinaryPRGGlobalFallbackLifetime.envelope parsed.1.1+128 := hAdd
    _ ≤ C₁*X^d₁+C₂*5^d₂*X^d₂+128 := by omega
    _ ≤ C₁*X^D+C₂*5^d₂*X^D+128*X^D := by
      have h128 : 128 ≤ 128*X^D := by nlinarith only [hOne]
      omega
    _ = (C₁+C₂*5^d₂+128)*X^D := by ring

theorem accepted_all_prefix (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (borrowed steps : ℕ) :
    retainedHeap borrowed
        (runWithTrace frame parsed hParsed store rich K outer scalar).2 steps ≤
        borrowed+envelope frame parsed.1 store K ∧
      framePeak
        ((runWithTrace frame parsed hParsed store rich K outer scalar).2.take steps) ≤
        envelope frame parsed.1 store K :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (accepted_usage frame parsed hParsed store rich K outer scalar) borrowed steps

theorem accepted_uniform_all_prefix :
    ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : PhysicalParsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (store : BinarySeedLookupTree.Store) (rich : Bool)
      (K : ℕ) (outer scalar : BinaryScalarTape K) (borrowed steps : ℕ),
      retainedHeap borrowed
          (runWithTrace frame parsed hParsed store rich K outer scalar).2 steps ≤
          borrowed+C*(frame.length+K+store.width+store.cap.value+3)^d ∧
        framePeak
          ((runWithTrace frame parsed hParsed store rich K outer scalar).2.take steps) ≤
          C*(frame.length+K+store.width+store.cap.value+3)^d := by
  obtain ⟨C,d,hUsage⟩ := accepted_uniform_polynomial
  exact ⟨C,d,fun frame parsed hParsed store rich K outer scalar borrowed steps =>
    BinaryPRGHeapTraceUsage.all_prefix _ _
      (hUsage frame parsed hParsed store rich K outer scalar) borrowed steps⟩

end Blotto.BinaryTerminalPhysicalFixedLifetime
