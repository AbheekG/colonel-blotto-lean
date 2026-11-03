import Blotto.BinaryInitialTraceSparsity

/-! The actual persistent-write emission counter is forwarded separately from
all prior records and coin/source-emission fields. These bounds price named
source/emitter operations; native scalar/header/reference/allocator costs and
later cached/raw/pair ledger transport remain separate. -/
namespace Blotto.BinaryWriteEmissionTransport
open BinarySeedPreparationSpace
set_option autoImplicit false

variable {n : ℕ}

theorem source_writes_total (seed : BinarySeedLookupTree.Store)
    (request : BinaryPRGPhysicalRawRequestLifetime.Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryPhysicalHeapAllowanceInitial.sourceAt seed request rich pc hp).2+
      (BinaryPhysicalHeapAllowanceInitial.sourceAtMeasured seed request rich pc hp).2+
      (BinaryPhysicalHeapAllowanceInitial.sourceAtTraceMeasured seed request rich pc hp).2+
      (BinaryPhysicalHeapAllowanceInitial.sourceAtTraceWithWrites seed request rich pc hp).2 ≤
        98*(BinaryPhysicalHeapAllowanceInitial.sourceAt seed request rich pc hp).2+
          5*(BinaryPhysicalHeapAllowanceInitial.initialFromRequest request rich).1.2.length+16*n+20 := by
  have h := BinaryResourceTraceLength.source_total seed request rich pc hp
  have hw := BinaryPhysicalHeapAllowanceInitial.sourceAtTraceWithWrites_write_bound seed request rich pc hp
  omega

theorem native_writes_total (seed : BinarySeedLookupTree.Store)
    (request : BinaryPRGPhysicalRawRequestLifetime.Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    (BinaryPhysicalHeapAllowanceRequest.nativeAt seed request rich pc hp).2+
      (BinaryPhysicalHeapAllowanceRequest.nativeAtMeasured seed request rich pc hp).2.1+
      (BinaryPhysicalHeapAllowanceRequest.nativeAtMeasured seed request rich pc hp).2.2+
      (BinaryPhysicalHeapAllowanceRequest.nativeAtWithWrites seed request rich pc hp).2 ≤
        98*(BinaryPhysicalHeapAllowanceRequest.nativeAt seed request rich pc hp).2+
          5*(BinaryPhysicalHeapAllowanceInitial.initialFromRequest request rich).1.2.length+16*n+20 := by
  have h := BinaryResourceTraceLength.native_total seed request rich pc hp
  have hw := BinaryPhysicalHeapAllowanceRequest.nativeAtWithWrites_write_bound seed request rich pc hp
  omega

theorem accepted_source_writes : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool)
        (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value),
        (BinaryPhysicalHeapAllowanceInitial.sourceAt seed parsed.1.2 rich pc hp).2+
          (BinaryPhysicalHeapAllowanceInitial.sourceAtMeasured seed parsed.1.2 rich pc hp).2+
          (BinaryPhysicalHeapAllowanceInitial.sourceAtTraceMeasured seed parsed.1.2 rich pc hp).2+
          (BinaryPhysicalHeapAllowanceInitial.sourceAtTraceWithWrites seed parsed.1.2 rich pc hp).2 ≤
            98*(BinaryPhysicalHeapAllowanceInitial.sourceAt seed parsed.1.2 rich pc hp).2+C*(frame.length+3)^d := by
  obtain ⟨C,d,hOverhead⟩ := BinaryInitialTraceSparsity.accepted_initial_overhead
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich pc hp
  have h := source_writes_total seed parsed.1.2 rich pc hp
  have ho := hOverhead frame parsed hParsed rich
  omega

theorem accepted_native_writes : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool)
        (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value),
        (BinaryPhysicalHeapAllowanceRequest.nativeAt seed parsed.1.2 rich pc hp).2+
          (BinaryPhysicalHeapAllowanceRequest.nativeAtMeasured seed parsed.1.2 rich pc hp).2.1+
          (BinaryPhysicalHeapAllowanceRequest.nativeAtMeasured seed parsed.1.2 rich pc hp).2.2+
          (BinaryPhysicalHeapAllowanceRequest.nativeAtWithWrites seed parsed.1.2 rich pc hp).2 ≤
            98*(BinaryPhysicalHeapAllowanceRequest.nativeAt seed parsed.1.2 rich pc hp).2+C*(frame.length+3)^d := by
  obtain ⟨C,d,hOverhead⟩ := BinaryInitialTraceSparsity.accepted_initial_overhead
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed seed rich pc hp
  have h := native_writes_total seed parsed.1.2 rich pc hp
  have ho := hOverhead frame parsed hParsed rich
  omega

theorem accepted_native_charge_width : ∃ C d : ℕ,
    ∀ (frame : List Bool) (parsed : (Σ n,BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool),
      (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed →
      ∀ (seed : BinarySeedLookupTree.Store) (rich : Bool)
        (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value),
        binaryWordWidth ((BinaryPhysicalHeapAllowanceRequest.nativeAt seed parsed.1.2 rich pc hp).2+
          (BinaryPhysicalHeapAllowanceRequest.nativeAtMeasured seed parsed.1.2 rich pc hp).2.1+
          (BinaryPhysicalHeapAllowanceRequest.nativeAtMeasured seed parsed.1.2 rich pc hp).2.2+
          (BinaryPhysicalHeapAllowanceRequest.nativeAtWithWrites seed parsed.1.2 rich pc hp).2) ≤
            binaryWordWidth (98*(BinaryPhysicalHeapAllowanceRequest.nativeAt seed parsed.1.2 rich pc hp).2+C*(frame.length+3)^d) := by
  obtain ⟨C,d,hBound⟩ := accepted_native_writes
  exact ⟨C,d,fun frame parsed hParsed seed rich pc hp =>
    binaryWordWidth_mono (hBound frame parsed hParsed seed rich pc hp)⟩

end Blotto.BinaryWriteEmissionTransport
