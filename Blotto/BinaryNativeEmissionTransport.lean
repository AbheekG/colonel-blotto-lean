import Blotto.BinaryWriteEmissionTransport

/-! The native wrapper emits its source block and the actual materialization
plan together, forwarding the preceding primitive/coin/source/write fields.
Bounds count named source/emitter operations; complete native model pricing and
cached/raw/pair transport remain separate obligations. -/
namespace Blotto.BinaryNativeEmissionTransport
open BinarySeedPreparationSpace
set_option autoImplicit false
variable {n : ℕ}

theorem native_emission (seed : BinarySeedLookupTree.Store)
    (request : BinaryPRGPhysicalRawRequestLifetime.Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryPhysicalHeapAllowanceRequest.nativeAtWithEmission seed request rich pc hp).2 ≤
      130*(BinaryPhysicalHeapAllowanceRequest.nativeAt seed request rich pc hp).2+
        5*(BinaryPhysicalHeapAllowanceInitial.initialFromRequest request rich).1.2.length+10 := by
  have h := BinaryPhysicalHeapAllowanceRequest.nativeAtWithEmission_bound seed request rich pc hp
  have ht := BinaryResourceTraceLength.source_length seed request rich pc hp
  have hw := BinaryPhysicalHeapAllowanceRequest.nativeAt_source_work_le seed request rich pc hp
  omega

theorem native_total (seed : BinarySeedLookupTree.Store)
    (request : BinaryPRGPhysicalRawRequestLifetime.Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryPhysicalHeapAllowanceRequest.nativeAt seed request rich pc hp).2+
      (BinaryPhysicalHeapAllowanceRequest.nativeAtMeasured seed request rich pc hp).2.1+
      (BinaryPhysicalHeapAllowanceRequest.nativeAtMeasured seed request rich pc hp).2.2+
      (BinaryPhysicalHeapAllowanceRequest.nativeAtWithWrites seed request rich pc hp).2+
      (BinaryPhysicalHeapAllowanceRequest.nativeAtWithEmission seed request rich pc hp).2 ≤
        228*(BinaryPhysicalHeapAllowanceRequest.nativeAt seed request rich pc hp).2+
          10*(BinaryPhysicalHeapAllowanceInitial.initialFromRequest request rich).1.2.length+16*n+30 := by
  have h := BinaryWriteEmissionTransport.native_writes_total seed request rich pc hp
  have he := native_emission seed request rich pc hp
  omega

theorem native_record_total (seed : BinarySeedLookupTree.Store)
    (request : BinaryPRGPhysicalRawRequestLifetime.Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    let produced := BinaryPhysicalHeapAllowanceRequest.nativeAtWithEmission seed request rich pc hp
    produced.1.1.1.2+produced.1.1.2.1+produced.1.1.2.2+produced.1.2+produced.2 ≤
      228*produced.1.1.1.2+
        10*(BinaryPhysicalHeapAllowanceInitial.initialFromRequest request rich).1.2.length+16*n+30 :=
  native_total seed request rich pc hp

theorem accepted_native_emission : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool)
        (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value),
        (BinaryPhysicalHeapAllowanceRequest.nativeAtWithEmission seed parsed.1.2 rich pc hp).2 ≤
          130*(BinaryPhysicalHeapAllowanceRequest.nativeAt seed parsed.1.2 rich pc hp).2+C*(frame.length+3)^d := by
  obtain ⟨C,d,hOverhead⟩ := BinaryInitialTraceSparsity.accepted_initial_overhead
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich pc hp
  have h := native_emission seed parsed.1.2 rich pc hp
  have ho := hOverhead frame parsed hParsed rich
  omega

theorem accepted_native_total : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool)
        (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value),
        let produced := BinaryPhysicalHeapAllowanceRequest.nativeAtWithEmission seed parsed.1.2 rich pc hp
        produced.1.1.1.2+produced.1.1.2.1+produced.1.1.2.2+produced.1.2+produced.2 ≤
          228*produced.1.1.1.2+C*(frame.length+3)^d := by
  obtain ⟨C,d,hOverhead⟩ := BinaryInitialTraceSparsity.accepted_initial_overhead
  refine ⟨2*C,d,?_⟩
  intro frame parsed hParsed seed rich pc hp
  have h := native_record_total seed parsed.1.2 rich pc hp
  have ho := hOverhead frame parsed hParsed rich
  dsimp only at h ⊢
  simp only [Nat.mul_assoc]
  omega

theorem accepted_native_charge_width : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool)
        (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value),
        let produced := BinaryPhysicalHeapAllowanceRequest.nativeAtWithEmission seed parsed.1.2 rich pc hp
        binaryWordWidth (produced.1.1.1.2+produced.1.1.2.1+produced.1.1.2.2+produced.1.2+produced.2) ≤
          binaryWordWidth (228*produced.1.1.1.2+C*(frame.length+3)^d) := by
  obtain ⟨C,d,hBound⟩ := accepted_native_total
  exact ⟨C,d,fun frame parsed hParsed seed rich pc hp =>
    binaryWordWidth_mono (hBound frame parsed hParsed seed rich pc hp)⟩

end Blotto.BinaryNativeEmissionTransport
