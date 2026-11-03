import Blotto.BinaryTerminalPhysicalCertifiedPrefix
import Blotto.BinaryPRGHeapTerminalLifetime
import Blotto.BinaryPRGFullOutputLifetimePolynomial

/-! The accepted physical cache and its certificate feed the selected terminal
draw. Reference equalities and source promises are proof-only transports. -/
namespace Blotto.BinaryTerminalPhysicalDrawLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryPRGResourceWork BinaryPRGTerminalWork
open BinaryCachedGroupInputHeight
set_option maxHeartbeats 2000000

private abbrev PhysicalParsed :=
  (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool

theorem logical_success (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (result : BinaryPRGHeapCertifiedPrefixLifetime.CachedResult
      parsed.1.2.logical.request rich)
    (h : (BinaryTerminalPhysicalCertifiedPrefix.runWithTrace
      frame parsed hParsed store rich).1.1 = some result) :
    (BinaryPRGHeapCertifiedPrefixLifetime.runWithTrace store
      parsed.1.2.logical.request rich).1.1 = some result := by
  have he := congrArg Prod.fst
    (BinaryTerminalPhysicalCertifiedPrefix.accepted_logical_output
      frame parsed hParsed store rich)
  exact he.symm.trans h

theorem cursor_bound (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool) :
    (BinaryTerminalPhysicalCertifiedPrefix.runWithTrace
      frame parsed hParsed store rich).1.2.value ≤ store.cap.value := by
  have he := congrArg Prod.snd
    (BinaryTerminalPhysicalCertifiedPrefix.accepted_logical_output
      frame parsed hParsed store rich)
  rw [he]
  exact BinaryPRGHeapCertifiedPrefixProperties.cursor_bound store
    parsed.1.2.logical.request rich

def runWithTrace (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    BinaryPRGWordControllerTerminal.Result store parsed.1.1 × Trace :=
  let request := parsed.1.2.logical.request
  let observed := BinaryTerminalPhysicalCertifiedPrefix.runWithTrace
    frame parsed hParsed store rich
  match hSome : observed.1.1 with
  | none => ((none,observed.1.2),wrap 16 2 [observed.2])
  | some result =>
      let drawn := BinaryWordTerminalLifetime.runWithTrace store result.2
        (terminal_canonical request rich result.1)
        (BinaryPRGHeapCertifiedPrefixProperties.admissible store request rich result
          (logical_success frame parsed hParsed store rich result hSome))
        K outer scalar observed.1.2 (cursor_bound frame parsed hParsed store rich)
      (drawn.1,wrap 32 2 [observed.2,drawn.2])

theorem runWithTrace_none (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K)
    (h : (BinaryTerminalPhysicalCertifiedPrefix.runWithTrace
      frame parsed hParsed store rich).1.1 = none) :
    (runWithTrace frame parsed hParsed store rich K outer scalar).1 =
      (none,(BinaryTerminalPhysicalCertifiedPrefix.runWithTrace
        frame parsed hParsed store rich).1.2) := by
  unfold runWithTrace
  dsimp only
  split
  · rfl
  · rename_i result hOther
    cases h.symm.trans hOther

theorem runWithTrace_some (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K)
    (result : BinaryPRGHeapCertifiedPrefixLifetime.CachedResult
      parsed.1.2.logical.request rich)
    (h : (BinaryTerminalPhysicalCertifiedPrefix.runWithTrace
      frame parsed hParsed store rich).1.1 = some result) :
    (runWithTrace frame parsed hParsed store rich K outer scalar).1 =
      BinaryPRGWordControllerTerminal.runPrepared store
        (BinaryCachedTerminalPreparation.prepare
          (terminalInput parsed.1.2.logical.request rich result.1))
        (terminal_canonical parsed.1.2.logical.request rich result.1)
        (BinaryPRGHeapCertifiedPrefixProperties.admissible store
          parsed.1.2.logical.request rich result
          (logical_success frame parsed hParsed store rich result h))
        K outer scalar
        (BinaryTerminalPhysicalCertifiedPrefix.runWithTrace
          frame parsed hParsed store rich).1.2
        (cursor_bound frame parsed hParsed store rich) := by
  unfold runWithTrace
  dsimp only
  split
  · rename_i hOther
    cases hOther.symm.trans h
  · rename_i other hOther
    have he : other = result := Option.some.inj (hOther.symm.trans h)
    subst other
    rw [BinaryWordTerminalLifetime.runWithTrace_erasure]
    rw [(BinaryPRGHeapCertifiedPrefixProperties.reached store
      parsed.1.2.logical.request rich result
      (logical_success frame parsed hParsed store rich result h)).2]
    exact BinaryTerminalCacheCertificate.zeroWork_runPrepared _ _ _ _ _ _ _ _ _

theorem accepted_erasure (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (runWithTrace frame parsed hParsed store rich K outer scalar).1 =
      BinaryPRGWordControllerRequest.run store
        parsed.1.2.logical.request rich K outer scalar := by
  let request := parsed.1.2.logical.request
  have hPrefix := BinaryTerminalPhysicalCertifiedPrefix.accepted_reference
    frame parsed hParsed store rich
  have hPosition := congrArg Prod.snd hPrefix
  change (BinaryTerminalPhysicalCertifiedPrefix.runWithTrace
      frame parsed hParsed store rich).1.2 =
    (BinaryPRGWordControllerResource.requestRun store request rich).2 at hPosition
  have hReturned := congrArg Prod.fst hPrefix
  change (BinaryTerminalPhysicalCertifiedPrefix.runWithTrace
      frame parsed hParsed store rich).1.1 =
    (BinaryPRGWordControllerResource.requestRun store request rich).1.map
      (fun state =>
        (⟨state,BinaryTerminalCacheCertificate.zeroWork
          (BinaryCachedTerminalPreparation.prepare (terminalInput request rich state))⟩ :
          BinaryPRGHeapCertifiedPrefixLifetime.CachedResult request rich)) at hReturned
  unfold BinaryPRGWordControllerRequest.run
  dsimp only
  split
  · rename_i hNone
    have hEmpty : (BinaryTerminalPhysicalCertifiedPrefix.runWithTrace
        frame parsed hParsed store rich).1.1 = none := by
      rw [hReturned,hNone,Option.map_none]
      rfl
    rw [runWithTrace_none frame parsed hParsed store rich K outer scalar hEmpty,
      hPosition]
  · rename_i state hSome
    let result : BinaryPRGHeapCertifiedPrefixLifetime.CachedResult request rich :=
      ⟨state,BinaryTerminalCacheCertificate.zeroWork
        (BinaryCachedTerminalPreparation.prepare (terminalInput request rich state))⟩
    have hResult : (BinaryTerminalPhysicalCertifiedPrefix.runWithTrace
        frame parsed hParsed store rich).1.1 = some result := by
      rw [hReturned,hSome]
      rfl
    rw [runWithTrace_some frame parsed hParsed store rich K outer scalar result hResult]
    dsimp only [result]
    congr 1

theorem accepted_logical_output (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    (runWithTrace frame parsed hParsed store rich K outer scalar).1 =
      (BinaryPRGHeapTerminalLifetime.runWithTrace store
        parsed.1.2.logical.request rich K outer scalar).1 := by
  rw [accepted_erasure, BinaryPRGHeapTerminalLifetime.runWithTrace_erasure]

theorem accepted_state (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    BinaryPRGWordControllerRequest.decoded store
      (runWithTrace frame parsed hParsed store rich K outer scalar).1 =
      (BinaryPRGCachedPrimitiveRun.run parsed.1.2.logical.request rich K
        store.cap.value outer scalar (BinaryWordIndexCoinController.reader store)).1 := by
  rw [accepted_erasure]
  exact BinaryPRGWordControllerRequest.run_state store
    parsed.1.2.logical.request rich K outer scalar

noncomputable def envelope (frame : List Bool)
    (parsed : Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n)
    (store : BinarySeedLookupTree.Store) (K : ℕ) : ℕ :=
  BinaryTerminalPhysicalCertifiedPrefix.envelope frame parsed store+
    BinaryWordTerminalLifetime.envelope parsed.1
      (inputHeight parsed.2.logical.request) K store.width store.cap.value
      store.cap.value+128

theorem accepted_usage_additive (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    usage (runWithTrace frame parsed hParsed store rich K outer scalar).2 ≤
      usage (BinaryTerminalPhysicalCertifiedPrefix.runWithTrace
        frame parsed hParsed store rich).2+
        BinaryWordTerminalLifetime.envelope parsed.1.1
          (inputHeight parsed.1.2.logical.request) K store.width store.cap.value
          store.cap.value+128 := by
  let request := parsed.1.2.logical.request
  let observed := BinaryTerminalPhysicalCertifiedPrefix.runWithTrace
    frame parsed hParsed store rich
  unfold runWithTrace
  dsimp only
  split
  · have hw := wrap_usage 16 2 [observed.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 16 2 [observed.2]) ≤
      usage observed.2+
        BinaryWordTerminalLifetime.envelope parsed.1.1
          (inputHeight request) K store.width store.cap.value store.cap.value+128
    omega
  · rename_i result hSome
    have hLogical := logical_success frame parsed hParsed store rich result hSome
    have hs : 3 ≤ inputHeight request := by unfold inputHeight; omega
    let drawn := BinaryWordTerminalLifetime.runWithTrace store result.2
      (terminal_canonical request rich result.1)
      (BinaryPRGHeapCertifiedPrefixProperties.admissible store request rich result hLogical)
      K outer scalar observed.1.2 (cursor_bound frame parsed hParsed store rich)
    have hDraw := BinaryWordTerminalLifetime.runWithTrace_usage store result.2
      (terminal_canonical request rich result.1)
      (BinaryPRGHeapCertifiedPrefixProperties.admissible store request rich result hLogical)
      (inputHeight request) hs
      (BinaryPRGHeapCertifiedPrefixProperties.uniform_height store request rich result hLogical)
      (BinaryPRGHeapCertifiedPrefixProperties.mixed_height store request rich result hLogical)
      (BinaryPRGHeapCertifiedPrefixProperties.route_height store request rich result hLogical)
      K outer scalar observed.1.2 (cursor_bound frame parsed hParsed store rich)
    change usage drawn.2 ≤ _ at hDraw
    have hMono := BinaryWordTerminalLifetime.envelope_remaining_mono
      parsed.1.1 (inputHeight request) K store.width store.cap.value
      (store.cap.value-observed.1.2.value) store.cap.value (Nat.sub_le _ _)
    have hw := wrap_usage 32 2 [observed.2,drawn.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 32 2 [observed.2,drawn.2]) ≤
      usage observed.2+
        BinaryWordTerminalLifetime.envelope parsed.1.1
          (inputHeight request) K store.width store.cap.value store.cap.value+128
    dsimp only [request] at *
    omega

theorem accepted_usage (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    usage (runWithTrace frame parsed hParsed store rich K outer scalar).2 ≤
      envelope frame parsed.1 store K := by
  have hAdd := accepted_usage_additive frame parsed hParsed store rich K outer scalar
  have hPrefix := BinaryTerminalPhysicalCertifiedPrefix.accepted_usage
    frame parsed hParsed store rich
  unfold envelope
  omega

theorem accepted_uniform_polynomial :
    ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : PhysicalParsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (store : BinarySeedLookupTree.Store) (rich : Bool)
      (K : ℕ) (outer scalar : BinaryScalarTape K),
      usage (runWithTrace frame parsed hParsed store rich K outer scalar).2 ≤
        C*(frame.length+K+store.width+store.cap.value+3)^d := by
  obtain ⟨C₁,d₁,hCert⟩ :=
    BinaryTerminalPhysicalCertifiedPrefix.accepted_uniform_polynomial
  obtain ⟨C₂,d₂,hCont⟩ :=
    BinaryPRGFullOutputLifetimePolynomial.continuation_polynomial
  refine ⟨C₁+C₂*5^d₂+128,max d₁ d₂,?_⟩
  intro frame parsed hParsed store rich K outer scalar
  let request := parsed.1.2.logical.request
  let s := request.source.originalInputWordWidth
  let X := frame.length+K+store.width+store.cap.value+3
  let D := max d₁ d₂
  have hX : 0 < X := by dsimp only [X]; omega
  have hn := BinaryTerminalPhysicalRouteLifetime.accepted_dimension
    frame parsed hParsed
  have hs := BinaryTerminalPhysicalRouteLifetime.accepted_source_width
    frame parsed hParsed
  have hCertBound := hCert frame parsed hParsed store rich
  have hCertBase : frame.length+store.width+store.cap.value+3 ≤ X := by
    dsimp only [X]
    omega
  have hCertTop :
      usage (BinaryTerminalPhysicalCertifiedPrefix.runWithTrace
        frame parsed hParsed store rich).2 ≤ C₁*X^d₁ := by
    exact hCertBound.trans (Nat.mul_le_mul_left C₁
      (Nat.pow_le_pow_left hCertBase d₁))
  have hContBound := hCont
    ⟨parsed.1.1,s,K,store.width,store.cap.value,0⟩
  change BinaryPRGFullOutputLifetimePolynomial.continuationEnvelope
      parsed.1.1 s K store.width store.cap.value 0 ≤
        C₂*(parsed.1.1+s+K+store.width+store.cap.value+1)^d₂ at hContBound
  have hTermBase : BinaryWordTerminalLifetime.envelope parsed.1.1
      (inputHeight request) K store.width store.cap.value store.cap.value ≤
      BinaryPRGFullOutputLifetimePolynomial.continuationEnvelope
        parsed.1.1 s K store.width store.cap.value 0 := by
    change BinaryWordTerminalLifetime.envelope parsed.1.1
      (4*(s+2)) K store.width store.cap.value store.cap.value ≤ _
    dsimp only [BinaryPRGFullOutputLifetimePolynomial.continuationEnvelope]
    omega
  have hSize : parsed.1.1+s+K+store.width+store.cap.value+1 ≤ 5*X := by
    dsimp only [s,request,X] at *
    omega
  have hTermTop : BinaryWordTerminalLifetime.envelope parsed.1.1
      (inputHeight request) K store.width store.cap.value store.cap.value ≤
      C₂*5^d₂*X^d₂ := by
    have hp := Nat.mul_le_mul_left C₂ (Nat.pow_le_pow_left hSize d₂)
    rw [Nat.mul_pow] at hp
    exact (hTermBase.trans hContBound).trans (hp.trans_eq (by ring))
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
    _ ≤ usage (BinaryTerminalPhysicalCertifiedPrefix.runWithTrace
          frame parsed hParsed store rich).2+
        BinaryWordTerminalLifetime.envelope parsed.1.1
          (inputHeight request) K store.width store.cap.value store.cap.value+128 := hAdd
    _ ≤ C₁*X^d₁+C₂*5^d₂*X^d₂+128 := by omega
    _ ≤ C₁*X^D+C₂*5^d₂*X^D+128*X^D := by
      have h128 : 128 ≤ 128*X^D := by nlinarith only [hOne]
      omega
    _ = (C₁+C₂*5^d₂+128)*X^D := by ring

theorem accepted_all_prefix (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) (borrowed steps : ℕ) :
    retainedHeap borrowed (runWithTrace frame parsed hParsed store rich K outer scalar).2 steps ≤
        borrowed+envelope frame parsed.1 store K ∧
      framePeak ((runWithTrace frame parsed hParsed store rich K outer scalar).2.take steps) ≤
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

end Blotto.BinaryTerminalPhysicalDrawLifetime
