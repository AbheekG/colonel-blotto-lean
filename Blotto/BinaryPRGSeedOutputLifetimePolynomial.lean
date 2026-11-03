import Blotto.BinaryPRGPhysicalOutputPolynomial

/-! Full seed validation/preparation and physical original-budget output have
a uniform polynomial retained-cell/activation envelope. Accepted raw request
length derives its parameters, including all rejected seeds. Raw request
parsing/preparation itself is not yet included in this trace. -/
namespace Blotto.BinaryPRGSeedOutputLifetimePolynomial
open BinaryPRGFullOutputLifetimePolynomial BinaryPRGHeapTraceUsage BinarySeedPreparationSpace
open RationalLottoResourceSystem
set_option maxHeartbeats 20000000
set_option maxRecDepth 20000

theorem wordWidth_le (N : ℕ) : binaryWordWidth N ≤ N+1 := by
  unfold binaryWordWidth
  exact Nat.add_le_add_right (Nat.log2_le_self N) 1

theorem header_length {n : ℕ} (header : BinaryPRGHeaderFrame.Header n) : header.bytes.length ≤ 2*n+3 := by
  rw [header.correct,BinaryNatFrame.encode_length]
  have h := wordWidth_le n
  omega

theorem table_envelope_polynomial : ∃ C d : ℕ,∀ {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision),
    BinaryPRGHeapSeedTableOutputLifetime.envelope prepared tables ≤
      C*(n+prepared.request.source.originalInputWordWidth+prepared.request.precision+
        coinBitBudget n prepared.request.precision+2)^d := by
  rcases BinaryPRGPhysicalOutputPolynomial.framed_envelope_polynomial with ⟨C,d,hBound⟩
  refine ⟨C*3^d+128,d+1,?_⟩
  intro n prepared tables
  let N := coinBitBudget n prepared.request.precision
  let store := BinarySeedLookupTree.prepare tables.choice.data.toList
  let X := n+prepared.request.source.originalInputWordWidth+prepared.request.precision+N+2
  have hStore := BinaryPRGHeapSeedTableOutputLifetime.store_dimensions prepared tables
  have hi : store.width ≤ N+1 := hStore.2.trans (wordWidth_le N)
  have hb : store.cap.value = N := hStore.1
  have hHeader := header_length prepared.header
  have hSize : n+prepared.request.source.originalInputWordWidth+prepared.request.precision+
      store.width+store.cap.value+prepared.header.bytes.length+2 ≤ 3*X := by dsimp [X]; omega
  have hX : 0 < X := by dsimp [X]; omega
  have hPow := Nat.pow_le_pow_left hSize d
  rw [Nat.mul_pow] at hPow
  have hUp : X^d ≤ X^(d+1) := Nat.pow_le_pow_right hX (by omega)
  have hPow' := hPow.trans (Nat.mul_le_mul_left (3^d) hUp)
  have hOut := hBound prepared.request prepared.request.precision store.width store.cap.value prepared.header.bytes.length
  have hScale := Nat.mul_le_mul_left C hPow'
  have hFrame : BinaryPRGPhysicalFramedLifetime.envelope prepared.request prepared.request.precision
      store.width store.cap.value prepared.header.bytes.length ≤ (C*3^d)*X^(d+1) := by nlinarith
  have hLinear : N ≤ X^(d+1) := by
    have hNX : N ≤ X := by dsimp [X]; omega
    exact hNX.trans (by simpa only [pow_one] using Nat.pow_le_pow_right hX (show 1 ≤ d+1 by omega))
  have hOne := Nat.one_le_pow (d+1) X hX
  have hWord := wordWidth_le N
  change BinaryPRGPhysicalFramedLifetime.envelope prepared.request prepared.request.precision store.width store.cap.value
    prepared.header.bytes.length+50*N+binaryWordWidth N+64 ≤ (C*3^d+128)*X^(d+1)
  nlinarith

def seedJoinEnvelope (C d n s K : ℕ) : ℕ :=
  BinaryPRGHeapSeedOutputLifetime.preparationEnvelope n K+
    C*(n+s+K+coinBitBudget n K+2)^d+128

theorem seedJoin_polynomial (C d : ℕ) : NaturalPolynomialEnvelope inputSize (fun p =>
    seedJoinEnvelope C d p.count p.height p.precision) := by
  unfold seedJoinEnvelope
  output_lifetime_polynomial

theorem uniform_envelope : ∃ C d : ℕ,∀ {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (seed : List Bool),
    BinaryPRGHeapSeedOutputLifetime.envelope prepared seed ≤
      C*(n+prepared.request.source.originalInputWordWidth+prepared.request.precision+2)^d := by
  rcases table_envelope_polynomial with ⟨C₁,d₁,h₁⟩
  rcases seedJoin_polynomial C₁ d₁ with ⟨C,d,hBound⟩
  refine ⟨C,d,?_⟩
  intro n prepared seed
  have hOption : ((BinaryPRGSeedBlocks.read n prepared.request.precision seed).1.map
      (BinaryPRGHeapSeedTableOutputLifetime.envelope prepared)).getD 0 ≤
        C₁*(n+prepared.request.source.originalInputWordWidth+prepared.request.precision+
          coinBitBudget n prepared.request.precision+2)^d₁ := by
    cases (BinaryPRGSeedBlocks.read n prepared.request.precision seed).1 with
    | none => exact Nat.zero_le _
    | some tables => exact h₁ prepared tables
  have h := hBound ⟨n,prepared.request.source.originalInputWordWidth,prepared.request.precision,0,0,0⟩
  change seedJoinEnvelope C₁ d₁ n prepared.request.source.originalInputWordWidth prepared.request.precision ≤
    C*(n+prepared.request.source.originalInputWordWidth+prepared.request.precision+1)^d at h
  have hMono := Nat.mul_le_mul_left C (Nat.pow_le_pow_left (show n+prepared.request.source.originalInputWordWidth+
    prepared.request.precision+1 ≤ n+prepared.request.source.originalInputWordWidth+prepared.request.precision+2 by omega) d)
  unfold BinaryPRGHeapSeedOutputLifetime.envelope
  unfold seedJoinEnvelope at h
  omega

theorem uniform_usage : ∃ C d : ℕ,∀ {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n)
    (rich : Bool) (seed : List Bool), usage (BinaryPRGHeapSeedOutputLifetime.runWithTrace prepared rich seed).2 ≤
      C*(n+prepared.request.source.originalInputWordWidth+prepared.request.precision+2)^d := by
  rcases uniform_envelope with ⟨C,d,hBound⟩
  exact ⟨C,d,fun prepared rich seed =>
    (BinaryPRGHeapSeedOutputLifetime.runWithTrace_usage prepared rich seed).trans (hBound prepared seed)⟩

theorem uniform_all_prefix : ∃ C d : ℕ,∀ {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n)
    (rich : Bool) (seed : List Bool) (borrowed steps : ℕ),
    retainedHeap (borrowed+seed.length) (BinaryPRGHeapSeedOutputLifetime.runWithTrace prepared rich seed).2 steps ≤
      borrowed+seed.length+C*(n+prepared.request.source.originalInputWordWidth+prepared.request.precision+2)^d ∧
    framePeak ((BinaryPRGHeapSeedOutputLifetime.runWithTrace prepared rich seed).2.take steps) ≤
      C*(n+prepared.request.source.originalInputWordWidth+prepared.request.precision+2)^d := by
  rcases uniform_usage with ⟨C,d,hBound⟩
  exact ⟨C,d,fun prepared rich seed borrowed steps =>
    BinaryPRGHeapTraceUsage.all_prefix _ _ (hBound prepared rich seed) _ steps⟩

theorem parsed_all_prefix : ∃ C d : ℕ,∀ (frame : List Bool)
    (parsed : (Σ n,BinaryPRGAccuracyRulerRequest.Request n) × List Bool),
    (BinaryPRGAccuracyRulerRequest.read frame).1 = some parsed →
    ∀ (rich : Bool) (seed : List Bool) (borrowed steps : ℕ),
    retainedHeap (borrowed+seed.length) (BinaryPRGHeapSeedOutputLifetime.runWithTrace parsed.1.2 rich seed).2 steps ≤
      borrowed+seed.length+C*(frame.length+1)^d ∧
    framePeak ((BinaryPRGHeapSeedOutputLifetime.runWithTrace parsed.1.2 rich seed).2.take steps) ≤ C*(frame.length+1)^d := by
  rcases uniform_usage with ⟨C,d,hBound⟩
  refine ⟨C*13^d,d,?_⟩
  intro frame parsed hParsed rich seed borrowed steps
  have hn := BinaryPRGSeedRequestBound.read_dimension_bound frame parsed hParsed
  have hs := BinaryPRGFrameCostJoin.read_source_width frame parsed hParsed
  have hK := BinaryPRGAccuracyRulerRequest.read_precision_bound frame parsed hParsed
  have hSize : parsed.1.1+parsed.1.2.request.source.originalInputWordWidth+parsed.1.2.request.precision+2 ≤
      13*(frame.length+1) := by omega
  have h := (hBound parsed.1.2 rich seed).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d))
  rw [Nat.mul_pow] at h
  have hTop : usage (BinaryPRGHeapSeedOutputLifetime.runWithTrace parsed.1.2 rich seed).2 ≤
      (C*13^d)*(frame.length+1)^d := by nlinarith
  exact BinaryPRGHeapTraceUsage.all_prefix _ _ hTop _ steps

end Blotto.BinaryPRGSeedOutputLifetimePolynomial
