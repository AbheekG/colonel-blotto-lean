import Blotto.BinaryTerminalPhysicalFixedLifetime
import Blotto.BinaryPRGPhysicalFramedLifetime
import Blotto.BinaryPRGPhysicalOutputPolynomial

/-! The accepted physical terminal path continues through global fallback,
physical original-budget scaling, and direct output framing. -/
namespace Blotto.BinaryTerminalPhysicalFramedLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryPRGHeapFixedProperties
set_option maxHeartbeats 3000000

private abbrev PhysicalParsed :=
  (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool

def runWithTrace (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (List Bool × FixedBinaryWord store.width) × Trace :=
  let request := parsed.1.2.logical.request
  let drawn := BinaryTerminalPhysicalFixedLifetime.runWithTrace
    frame parsed hParsed store rich K outer scalar
  let output := BinaryPhysicalOutputLifetime.outputWithTrace
    request.prepared.original.a header.bytes drawn.1.1.data.toList
  ((output.1,drawn.1.2),wrapList parsed.1.1 32 (parsed.1.1+2)
    [drawn.2,output.2])

theorem accepted_output (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (runWithTrace frame parsed hParsed store rich K outer scalar header).1 =
      (BinaryPRGPhysicalFramedLifetime.runWithTrace store
        parsed.1.2.logical.request rich K outer scalar header).1 := by
  simp only [runWithTrace,BinaryPRGPhysicalFramedLifetime.runWithTrace,
    BinaryTerminalPhysicalFixedLifetime.accepted_logical_output]

theorem accepted_bytes (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (runWithTrace frame parsed hParsed store rich K outer scalar header).1.1 =
      BinaryStoredRowFrame.row (BinaryPRGWordControllerRequest.originalFixedSample
        store parsed.1.2.logical.request rich K outer scalar) := by
  rw [accepted_output]
  exact BinaryPRGPhysicalFramedLifetime.run_bytes store
    parsed.1.2.logical.request rich K outer scalar header

theorem accepted_cursor (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    (runWithTrace frame parsed hParsed store rich K outer scalar header).1.2 =
      (BinaryPRGWordControllerRequest.run store
        parsed.1.2.logical.request rich K outer scalar).2 := by
  rw [accepted_output]
  exact BinaryPRGPhysicalFramedLifetime.run_cursor store
    parsed.1.2.logical.request rich K outer scalar header

theorem accepted_read (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) (suffix : List Bool) :
    BinaryRatListFrame.readRow
        ((runWithTrace frame parsed hParsed store rich K outer scalar header).1.1++suffix) =
      some (parsed.1.1,List.ofFn (fun j => value
        ((BinaryPRGWordControllerRequest.originalFixedSample store
          parsed.1.2.logical.request rich K outer scalar).read j)),suffix) := by
  rw [accepted_output]
  rw [BinaryPRGPhysicalFramedLifetime.run_state]
  exact BinaryPRGHeapFramedLifetime.runWithTrace_read store
    parsed.1.2.logical.request rich K outer scalar header suffix

noncomputable def envelope (frame : List Bool)
    (parsed : Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n)
    (store : BinarySeedLookupTree.Store) (K headerLength : ℕ) : ℕ :=
  BinaryTerminalPhysicalFixedLifetime.envelope frame parsed store K+
    BinaryPhysicalOutputLifetime.bound parsed.1
      (wordWidth parsed.2.logical.request K) headerLength+
    2*(parsed.1+1)^2+64

theorem accepted_usage_additive (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    usage (runWithTrace frame parsed hParsed store rich K outer scalar header).2 ≤
      usage (BinaryTerminalPhysicalFixedLifetime.runWithTrace
        frame parsed hParsed store rich K outer scalar).2+
      BinaryPhysicalOutputLifetime.bound parsed.1.1
        (wordWidth parsed.1.2.logical.request K) header.bytes.length+
      2*(parsed.1.1+1)^2+64 := by
  let request := parsed.1.2.logical.request
  let drawn := BinaryTerminalPhysicalFixedLifetime.runWithTrace
    frame parsed hParsed store rich K outer scalar
  let output := BinaryPhysicalOutputLifetime.outputWithTrace
    request.prepared.original.a header.bytes drawn.1.1.data.toList
  have hRows : ∀ word ∈ drawn.1.1.data.toList,
      BinaryRationalOpcode.Valid word ∧ width word ≤ wordWidth request K := by
    have he := congrArg Prod.fst
      (BinaryTerminalPhysicalFixedLifetime.accepted_logical_output
        frame parsed hParsed store rich K outer scalar)
    change drawn.1.1 = (BinaryPRGHeapFixedLifetime.runWithTrace
      store request rich K outer scalar).1.1 at he
    rw [he,← BinaryPRGPhysicalFramedLifetime.table_list]
    intro word hw
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
    exact ⟨(BinaryPRGHeapFixedLifetime.runWithTrace_canonical
      store request rich K outer scalar j).1,
      row_width store request rich K outer scalar j⟩
  have ho := BinaryPhysicalOutputLifetime.output_usage
    request.prepared.original.a header.bytes drawn.1.1.data.toList
    request.valid.2.1.1.1 (wordWidth request K) (scale_width request K) hRows
  have hLength : drawn.1.1.data.toList.length = parsed.1.1 := by
    rw [Array.length_toList,drawn.1.1.size]
  rw [hLength] at ho
  have hw := wrapList_usage parsed.1.1 32 (parsed.1.1+2)
    [drawn.2,output.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (runWithTrace frame parsed hParsed store rich K outer scalar header).2 ≤ _ at hw
  change usage output.2 ≤ _ at ho
  have hn : 2*parsed.1.1 ≤ 2*(parsed.1.1+1)^2 := by nlinarith
  change usage (runWithTrace frame parsed hParsed store rich K outer scalar header).2 ≤
    usage drawn.2+BinaryPhysicalOutputLifetime.bound parsed.1.1
      (wordWidth request K) header.bytes.length+2*(parsed.1.1+1)^2+64
  dsimp only [request] at *
  omega

theorem accepted_usage (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    usage (runWithTrace frame parsed hParsed store rich K outer scalar header).2 ≤
      envelope frame parsed.1 store K header.bytes.length := by
  have hAdd := accepted_usage_additive frame parsed hParsed store rich K outer scalar header
  have hFixed := BinaryTerminalPhysicalFixedLifetime.accepted_usage
    frame parsed hParsed store rich K outer scalar
  unfold envelope
  omega

theorem accepted_uniform_polynomial :
    ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : PhysicalParsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (store : BinarySeedLookupTree.Store) (rich : Bool)
      (K : ℕ) (outer scalar : BinaryScalarTape K)
      (header : BinaryPRGHeaderFrame.Header parsed.1.1),
      usage (runWithTrace frame parsed hParsed store rich K outer scalar header).2 ≤
        C*(frame.length+K+store.width+store.cap.value+header.bytes.length+3)^d := by
  obtain ⟨C₁,d₁,hFixed⟩ :=
    BinaryTerminalPhysicalFixedLifetime.accepted_uniform_polynomial
  obtain ⟨C₂,d₂,hExtra⟩ :=
    BinaryPRGPhysicalOutputPolynomial.extra_polynomial
  refine ⟨C₁+C₂*5^d₂+66,max d₁ (max d₂ 2),?_⟩
  intro frame parsed hParsed store rich K outer scalar header
  let request := parsed.1.2.logical.request
  let s := request.source.originalInputWordWidth
  let X := frame.length+K+store.width+store.cap.value+header.bytes.length+3
  let D := max d₁ (max d₂ 2)
  have hX : 0 < X := by dsimp only [X]; omega
  have hn := BinaryTerminalPhysicalRouteLifetime.accepted_dimension
    frame parsed hParsed
  have hs := BinaryTerminalPhysicalRouteLifetime.accepted_source_width
    frame parsed hParsed
  have hF := hFixed frame parsed hParsed store rich K outer scalar
  have hFixedBase : frame.length+K+store.width+store.cap.value+3 ≤ X := by
    dsimp only [X]
    omega
  have hFixedTop : usage (BinaryTerminalPhysicalFixedLifetime.runWithTrace
      frame parsed hParsed store rich K outer scalar).2 ≤ C₁*X^d₁ := by
    exact hF.trans (Nat.mul_le_mul_left C₁
      (Nat.pow_le_pow_left hFixedBase d₁))
  have hExtraBound := hExtra
    ⟨parsed.1.1,s,K,store.width,store.cap.value,header.bytes.length⟩
  change BinaryPRGPhysicalOutputPolynomial.extraEnvelope
      parsed.1.1 s K header.bytes.length ≤
        C₂*(parsed.1.1+s+K+store.width+store.cap.value+
          header.bytes.length+1)^d₂ at hExtraBound
  have hPhysicalBase : BinaryPhysicalOutputLifetime.bound parsed.1.1
      (wordWidth request K) header.bytes.length ≤
      BinaryPRGPhysicalOutputPolynomial.extraEnvelope
        parsed.1.1 s K header.bytes.length := by
    change BinaryPhysicalOutputLifetime.bound parsed.1.1
      (1+2*expressionHeightBudget (max (3+s) (K+2)) 75)
      header.bytes.length ≤ _
    dsimp only [BinaryPRGPhysicalOutputPolynomial.extraEnvelope,
      BinaryPRGPhysicalOutputPolynomial.extraEnvelopeAt]
    omega
  have hSize : parsed.1.1+s+K+store.width+store.cap.value+
      header.bytes.length+1 ≤ 5*X := by
    dsimp only [s,request,X] at *
    omega
  have hPhysicalTop : BinaryPhysicalOutputLifetime.bound parsed.1.1
      (wordWidth request K) header.bytes.length ≤ C₂*5^d₂*X^d₂ := by
    have hp := Nat.mul_le_mul_left C₂ (Nat.pow_le_pow_left hSize d₂)
    rw [Nat.mul_pow] at hp
    exact (hPhysicalBase.trans hExtraBound).trans (hp.trans_eq (by ring))
  have hAdd := accepted_usage_additive frame parsed hParsed store rich K outer scalar header
  have h₁ : X^d₁ ≤ X^D :=
    Nat.pow_le_pow_right hX (Nat.le_max_left d₁ (max d₂ 2))
  have h₂ : X^d₂ ≤ X^D :=
    Nat.pow_le_pow_right hX ((Nat.le_max_left d₂ 2).trans (Nat.le_max_right d₁ (max d₂ 2)))
  have h₂sq : X^2 ≤ X^D :=
    Nat.pow_le_pow_right hX ((Nat.le_max_right d₂ 2).trans (Nat.le_max_right d₁ (max d₂ 2)))
  have hOne : 1 ≤ X^D := Nat.one_le_pow D X (by omega)
  have hScale₁ := Nat.mul_le_mul_left C₁ h₁
  have hScale₂ := Nat.mul_le_mul_left (C₂*5^d₂) h₂
  have hN : parsed.1.1+1 ≤ X := by dsimp only [X]; omega
  have hNSq := Nat.mul_le_mul_left 2
    ((Nat.pow_le_pow_left hN 2).trans h₂sq)
  have h64 : 64 ≤ 64*X^D := by nlinarith only [hOne]
  change usage (runWithTrace frame parsed hParsed store rich K outer scalar header).2 ≤
    (C₁+C₂*5^d₂+66)*X^D
  calc
    _ ≤ usage (BinaryTerminalPhysicalFixedLifetime.runWithTrace
          frame parsed hParsed store rich K outer scalar).2+
        BinaryPhysicalOutputLifetime.bound parsed.1.1
          (wordWidth request K) header.bytes.length+
        2*(parsed.1.1+1)^2+64 := hAdd
    _ ≤ C₁*X^d₁+C₂*5^d₂*X^d₂+2*(parsed.1.1+1)^2+64 := by omega
    _ ≤ C₁*X^D+C₂*5^d₂*X^D+66*X^D := by omega
    _ = (C₁+C₂*5^d₂+66)*X^D := by ring

theorem accepted_all_prefix (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) (borrowed steps : ℕ) :
    retainedHeap borrowed
        (runWithTrace frame parsed hParsed store rich K outer scalar header).2 steps ≤
        borrowed+envelope frame parsed.1 store K header.bytes.length ∧
      framePeak
        ((runWithTrace frame parsed hParsed store rich K outer scalar header).2.take steps) ≤
        envelope frame parsed.1 store K header.bytes.length :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (accepted_usage frame parsed hParsed store rich K outer scalar header) borrowed steps

theorem accepted_uniform_all_prefix :
    ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : PhysicalParsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (store : BinarySeedLookupTree.Store) (rich : Bool)
      (K : ℕ) (outer scalar : BinaryScalarTape K)
      (header : BinaryPRGHeaderFrame.Header parsed.1.1) (borrowed steps : ℕ),
      retainedHeap borrowed
          (runWithTrace frame parsed hParsed store rich K outer scalar header).2 steps ≤
          borrowed+C*(frame.length+K+store.width+store.cap.value+header.bytes.length+3)^d ∧
        framePeak
          ((runWithTrace frame parsed hParsed store rich K outer scalar header).2.take steps) ≤
          C*(frame.length+K+store.width+store.cap.value+header.bytes.length+3)^d := by
  obtain ⟨C,d,hUsage⟩ := accepted_uniform_polynomial
  exact ⟨C,d,fun frame parsed hParsed store rich K outer scalar header borrowed steps =>
    BinaryPRGHeapTraceUsage.all_prefix _ _
      (hUsage frame parsed hParsed store rich K outer scalar header) borrowed steps⟩

end Blotto.BinaryTerminalPhysicalFramedLifetime
