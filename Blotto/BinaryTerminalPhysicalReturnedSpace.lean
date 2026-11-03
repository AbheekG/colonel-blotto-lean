import Blotto.BinaryPhysicalHeapReturnedSpace
import Blotto.BinaryTerminalPhysicalFullRawLifetime

/-! Retained-source composition from the one-pass physical resource request
through the terminal cache and output stages. The envelopes preserve the
allowance from the actual returned builder heaps. They are proof observers,
not additional selected computations or a host allocator-space model. -/

namespace Blotto.BinaryTerminalPhysicalReturnedSpace
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage
open BinaryPRGPhysicalRawRequestLifetime (Request)
open BinaryTerminalPhysicalRouteLifetime
set_option autoImplicit false
set_option maxHeartbeats 3000000

abbrev PhysicalRequest := Σ n,Request n
abbrev Parsed := PhysicalRequest × List Bool

noncomputable def cacheOverhead (frame : List Bool) (parsed : PhysicalRequest) : ℕ :=
  let request := parsed.2.logical.request
  BinaryTerminalPrefixLifetime.prefixBound request+
    rawRouteEnvelope frame.length
      (1+2*binaryWordWidth request.source.normalizedInput.latticeDenominator)+
    2000000*(3+2*binaryWordWidth request.source.normalizedInput.latticeDenominator)^4+
    3*parsed.1+200

noncomputable def cachedEnvelope (frame : List Bool) (parsed : PhysicalRequest)
    (store : BinarySeedLookupTree.Store) (rich : Bool) : ℕ :=
  2000000200*(frame.length+3)^7+
    BinaryPhysicalHeapReturnedSpace.runEnvelope parsed.2 rich store.width store.cap.value+
    cacheOverhead frame parsed+30

theorem accepted_cached_usage (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool) :
    usage (runCachedPrefixWithTrace parsed.1 store rich).2 ≤
      cachedEnvelope frame parsed.1 store rich := by
  have hResource := BinaryPhysicalHeapReturnedSpace.accepted_selected_usage
    frame parsed hParsed store rich
  rw [BinaryPhysicalHeapRequestLifetime.runWithTraceAndResidualAndBuildWork_erases]
    at hResource
  rw [runCachedPrefixWithTrace,runCachedPrefixWithTraceAndWork_erases]
  unfold runCachedPrefixWithTraceReference
  dsimp only
  cases hState : (BinaryPhysicalHeapRequestLifetime.runWithTrace
      store parsed.1.2 rich).1.1 with
  | none =>
      have hw := wrap_usage 16 2
        [(BinaryPhysicalHeapRequestLifetime.runWithTrace store parsed.1.2 rich).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 16 2
        [(BinaryPhysicalHeapRequestLifetime.runWithTrace store parsed.1.2 rich).2]) ≤ _
      unfold cachedEnvelope
      omega
  | some state =>
      have hOld : (BinaryPRGHeapRequestLifetime.run store
          parsed.1.2.logical.request rich).1.1 = some state := by
        rw [← BinaryPhysicalHeapRequestLifetime.run_erasure]
        exact hState
      have hCache := accepted_reached_cache_raw_usage frame parsed hParsed rich
        store state hOld
      change usage (cacheWithTrace
        (BinaryPRGTerminalWork.terminalInput parsed.1.2.logical.request rich state)
        parsed.1.2.physical.lengthStore).2 ≤ cacheOverhead frame parsed.1 at hCache
      have hw := wrap_usage 24 2
        [(BinaryPhysicalHeapRequestLifetime.runWithTrace store parsed.1.2 rich).2,
          (cacheWithTrace
            (BinaryPRGTerminalWork.terminalInput parsed.1.2.logical.request rich state)
            parsed.1.2.physical.lengthStore).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 24 2
        [(BinaryPhysicalHeapRequestLifetime.runWithTrace store parsed.1.2 rich).2,
          (cacheWithTrace
            (BinaryPRGTerminalWork.terminalInput parsed.1.2.logical.request rich state)
            parsed.1.2.physical.lengthStore).2]) ≤ _
      unfold cachedEnvelope
      omega

theorem cachedEnvelope_le_existing (frame : List Bool) (parsed : PhysicalRequest)
    (store : BinarySeedLookupTree.Store) (rich : Bool) :
    cachedEnvelope frame parsed store rich ≤ cachedPrefixEnvelope frame parsed store := by
  have hRequest := BinaryPhysicalHeapReturnedSpace.runEnvelope_le_input
    parsed.2 rich store.width store.cap.value
  have hArithmetic : 1+2*binaryWordWidth
      parsed.2.logical.request.source.normalizedInput.latticeDenominator+2 =
      3+2*binaryWordWidth
        parsed.2.logical.request.source.normalizedInput.latticeDenominator := by omega
  unfold cachedEnvelope cacheOverhead cachedPrefixEnvelope
  dsimp only
  simp only [hArithmetic]
  omega

noncomputable def certifiedEnvelope (frame : List Bool) (parsed : PhysicalRequest)
    (store : BinarySeedLookupTree.Store) (rich : Bool) : ℕ :=
  cachedEnvelope frame parsed store rich+96

theorem accepted_certified_usage (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool) :
    usage (BinaryTerminalPhysicalCertifiedPrefix.runWithTrace
      frame parsed hParsed store rich).2 ≤
      certifiedEnvelope frame parsed.1 store rich := by
  have hAdd := BinaryTerminalPhysicalCertifiedPrefix.accepted_usage_additive
    frame parsed hParsed store rich
  have hCached := accepted_cached_usage frame parsed hParsed store rich
  unfold certifiedEnvelope
  omega

theorem certifiedEnvelope_le_existing (frame : List Bool) (parsed : PhysicalRequest)
    (store : BinarySeedLookupTree.Store) (rich : Bool) :
    certifiedEnvelope frame parsed store rich ≤
      BinaryTerminalPhysicalCertifiedPrefix.envelope frame parsed store := by
  have h := cachedEnvelope_le_existing frame parsed store rich
  unfold certifiedEnvelope BinaryTerminalPhysicalCertifiedPrefix.envelope
  omega

noncomputable def drawEnvelope (frame : List Bool) (parsed : PhysicalRequest)
    (store : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) : ℕ :=
  certifiedEnvelope frame parsed store rich+
    BinaryWordTerminalLifetime.envelope parsed.1
      (BinaryCachedGroupInputHeight.inputHeight parsed.2.logical.request)
      K store.width store.cap.value store.cap.value+128

theorem accepted_draw_usage (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    usage (BinaryTerminalPhysicalDrawLifetime.runWithTrace
      frame parsed hParsed store rich K outer scalar).2 ≤
      drawEnvelope frame parsed.1 store rich K := by
  have hAdd := BinaryTerminalPhysicalDrawLifetime.accepted_usage_additive
    frame parsed hParsed store rich K outer scalar
  have hCert := accepted_certified_usage frame parsed hParsed store rich
  unfold drawEnvelope
  omega

theorem drawEnvelope_le_existing (frame : List Bool) (parsed : PhysicalRequest)
    (store : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) :
    drawEnvelope frame parsed store rich K ≤
      BinaryTerminalPhysicalDrawLifetime.envelope frame parsed store K := by
  have h := certifiedEnvelope_le_existing frame parsed store rich
  unfold drawEnvelope BinaryTerminalPhysicalDrawLifetime.envelope
  omega

noncomputable def fixedEnvelope (frame : List Bool) (parsed : PhysicalRequest)
    (store : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) : ℕ :=
  drawEnvelope frame parsed store rich K+
    BinaryPRGGlobalFallbackLifetime.envelope parsed.1+128

theorem accepted_fixed_usage (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K) :
    usage (BinaryTerminalPhysicalFixedLifetime.runWithTrace
      frame parsed hParsed store rich K outer scalar).2 ≤
      fixedEnvelope frame parsed.1 store rich K := by
  have hAdd := BinaryTerminalPhysicalFixedLifetime.accepted_usage_additive
    frame parsed hParsed store rich K outer scalar
  have hDraw := accepted_draw_usage frame parsed hParsed store rich K outer scalar
  unfold fixedEnvelope
  omega

theorem fixedEnvelope_le_existing (frame : List Bool) (parsed : PhysicalRequest)
    (store : BinarySeedLookupTree.Store) (rich : Bool) (K : ℕ) :
    fixedEnvelope frame parsed store rich K ≤
      BinaryTerminalPhysicalFixedLifetime.envelope frame parsed store K := by
  have h := drawEnvelope_le_existing frame parsed store rich K
  unfold fixedEnvelope BinaryTerminalPhysicalFixedLifetime.envelope
  omega

noncomputable def framedEnvelope (frame : List Bool) (parsed : PhysicalRequest)
    (store : BinarySeedLookupTree.Store) (rich : Bool) (K headerLength : ℕ) : ℕ :=
  fixedEnvelope frame parsed store rich K+
    BinaryPhysicalOutputLifetime.bound parsed.1
      (BinaryPRGHeapFixedProperties.wordWidth parsed.2.logical.request K) headerLength+
    2*(parsed.1+1)^2+64

theorem accepted_framed_usage (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool)
    (K : ℕ) (outer scalar : BinaryScalarTape K)
    (header : BinaryPRGHeaderFrame.Header parsed.1.1) :
    usage (BinaryTerminalPhysicalFramedLifetime.runWithTrace
      frame parsed hParsed store rich K outer scalar header).2 ≤
      framedEnvelope frame parsed.1 store rich K header.bytes.length := by
  have hAdd := BinaryTerminalPhysicalFramedLifetime.accepted_usage_additive
    frame parsed hParsed store rich K outer scalar header
  have hFixed := accepted_fixed_usage frame parsed hParsed store rich K outer scalar
  unfold framedEnvelope
  omega

theorem framedEnvelope_le_existing (frame : List Bool) (parsed : PhysicalRequest)
    (store : BinarySeedLookupTree.Store) (rich : Bool) (K headerLength : ℕ) :
    framedEnvelope frame parsed store rich K headerLength ≤
      BinaryTerminalPhysicalFramedLifetime.envelope frame parsed store K headerLength := by
  have h := fixedEnvelope_le_existing frame parsed store rich K
  unfold framedEnvelope BinaryTerminalPhysicalFramedLifetime.envelope
  omega

noncomputable def outputEnvelope (frame : List Bool) (parsed : PhysicalRequest)
    (rich : Bool)
    (blocks : BinaryPRGTapeSeedBlocks.Blocks parsed.1
      parsed.2.logical.request.precision) : ℕ :=
  let store := BinarySeedLookupTree.prepare blocks.choice.bits
  framedEnvelope frame parsed store rich parsed.2.logical.request.precision
    parsed.2.logical.header.bytes.length+49*blocks.choice.bits.length+80

theorem accepted_output_usage (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool)
    (blocks : BinaryPRGTapeSeedBlocks.Blocks parsed.1.1
      parsed.1.2.logical.request.precision) :
    usage (BinaryTerminalPhysicalSeedOutputLifetime.outputWithTrace
      frame parsed hParsed rich blocks).2 ≤ outputEnvelope frame parsed.1 rich blocks := by
  have hAdd := BinaryTerminalPhysicalSeedOutputLifetime.output_usage_additive
    frame parsed hParsed rich blocks
  have hFramed := accepted_framed_usage frame parsed hParsed
    (BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits).1 rich
    parsed.1.2.logical.request.precision blocks.outer blocks.scalar
    parsed.1.2.logical.header
  have hStore := BinaryWordStoreLifetime.prepareWithTrace_erases blocks.choice.bits
  dsimp only [outputEnvelope]
  rw [← hStore]
  omega

theorem outputEnvelope_le_existing (frame : List Bool) (parsed : PhysicalRequest)
    (rich : Bool)
    (blocks : BinaryPRGTapeSeedBlocks.Blocks parsed.1
      parsed.2.logical.request.precision) :
    outputEnvelope frame parsed rich blocks ≤
      BinaryTerminalPhysicalSeedOutputLifetime.outputEnvelope frame parsed blocks := by
  have h := framedEnvelope_le_existing frame parsed
    (BinarySeedLookupTree.prepare blocks.choice.bits) rich
    parsed.2.logical.request.precision parsed.2.logical.header.bytes.length
  dsimp only [outputEnvelope,BinaryTerminalPhysicalSeedOutputLifetime.outputEnvelope]
  omega

noncomputable def seedEnvelope (frame : List Bool) (parsed : PhysicalRequest)
    (rich : Bool) (seed : List Bool) : ℕ :=
  BinaryPRGHeapSeedOutputLifetime.preparationEnvelope
    parsed.1 parsed.2.logical.request.precision+
    ((BinaryPRGTapeSeedBlocks.readWithTrace parsed.1
      parsed.2.logical.request.precision seed).1.map
        (outputEnvelope frame parsed rich)).getD 0+128

theorem accepted_seed_usage (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    usage (BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace
      frame parsed hParsed rich seed).2 ≤ seedEnvelope frame parsed.1 rich seed := by
  let blocks := BinaryPRGTapeSeedBlocks.readWithTrace parsed.1.1
    parsed.1.2.logical.request.precision seed
  have hPrep := BinaryPRGTapeSeedBlocks.read_usage parsed.1.1
    parsed.1.2.logical.request.precision seed
  change usage blocks.2 ≤ BinaryPRGHeapSeedOutputLifetime.preparationEnvelope
    parsed.1.1 parsed.1.2.logical.request.precision at hPrep
  unfold BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace
  rw [BinaryPRGBooleanSeedBlocks.read_same]
  dsimp only
  split
  · rename_i hNone
    have hw := wrap_usage 16 2 [blocks.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 16 2 [blocks.2]) ≤ _
    unfold seedEnvelope
    rw [hNone]
    simp only [Option.map_none,Option.getD_none]
    omega
  · rename_i tapes hSome
    have hOut := accepted_output_usage frame parsed hParsed rich tapes
    have hw := wrap_usage 32 2
      [blocks.2,(BinaryTerminalPhysicalSeedOutputLifetime.outputWithTrace
        frame parsed hParsed rich tapes).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 32 2
      [blocks.2,(BinaryTerminalPhysicalSeedOutputLifetime.outputWithTrace
        frame parsed hParsed rich tapes).2]) ≤ _
    unfold seedEnvelope
    rw [hSome]
    simp only [Option.map_some,Option.getD_some]
    omega

theorem seedEnvelope_le_existing (frame : List Bool) (parsed : PhysicalRequest)
    (rich : Bool) (seed : List Bool) :
    seedEnvelope frame parsed rich seed ≤
      BinaryTerminalPhysicalSeedOutputLifetime.envelope frame parsed seed := by
  unfold seedEnvelope BinaryTerminalPhysicalSeedOutputLifetime.envelope
  cases h : (BinaryPRGTapeSeedBlocks.readWithTrace parsed.1
      parsed.2.logical.request.precision seed).1 with
  | none => simp only [Option.map_none,Option.getD_none]; omega
  | some blocks =>
      simp only [Option.map_some,Option.getD_some]
      have hOut := outputEnvelope_le_existing frame parsed rich blocks
      omega

noncomputable def rawEnvelope (rich : Bool) (frame seed : List Bool) : ℕ :=
  BinaryPRGPhysicalRawRequestLifetime.envelope frame.length+
    ((BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1.map
      (fun parsed => if parsed.2 = [] then
        seedEnvelope frame parsed.1 rich seed else 0)).getD 0+128

theorem raw_usage (rich : Bool) (frame seed : List Bool) :
    usage (BinaryTerminalPhysicalFullRawLifetime.runWithTrace rich frame seed).2 ≤
      rawEnvelope rich frame seed := by
  have hRead := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_usage frame
  unfold BinaryTerminalPhysicalFullRawLifetime.runWithTrace
  dsimp only
  split
  · rename_i hNone
    have hw := wrap_usage 16 2
      [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 16 2
      [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]) ≤ _
    unfold rawEnvelope
    rw [hNone]
    simp only [Option.map_none,Option.getD_none]
    omega
  · rename_i parsed hSome
    split
    · rename_i hTail
      have hOut := accepted_seed_usage frame parsed hSome rich seed
      have hw := wrap_usage 32 2
        [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2,
          (BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace
            frame parsed hSome rich seed).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 32 2
        [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2,
          (BinaryTerminalPhysicalSeedOutputLifetime.runWithTrace
            frame parsed hSome rich seed).2]) ≤ _
      unfold rawEnvelope
      rw [hSome]
      simp only [Option.map_some,Option.getD_some,ite_eq_left hTail]
      omega
    · rename_i hTail
      have hw := wrap_usage 24 2
        [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 24 2
        [(BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).2]) ≤ _
      unfold rawEnvelope
      rw [hSome]
      simp only [Option.map_some,Option.getD_some,ite_eq_right hTail]
      omega

theorem rawEnvelope_le_existing (rich : Bool) (frame seed : List Bool) :
    rawEnvelope rich frame seed ≤ BinaryTerminalPhysicalFullRawLifetime.envelope frame seed := by
  unfold rawEnvelope BinaryTerminalPhysicalFullRawLifetime.envelope
  cases h : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 with
  | none => simp only [Option.map_none,Option.getD_none]; omega
  | some parsed =>
      simp only [Option.map_some,Option.getD_some]
      by_cases hTail : parsed.2 = []
      · simp only [ite_eq_left hTail]
        have hSeed := seedEnvelope_le_existing frame parsed.1 rich seed
        omega
      · simp only [ite_eq_right hTail]
        omega

theorem accepted_cached_all_prefix (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (store : BinarySeedLookupTree.Store) (rich : Bool) (borrowed steps : ℕ) :
    retainedHeap borrowed (runCachedPrefixWithTrace parsed.1 store rich).2 steps ≤
        borrowed+cachedEnvelope frame parsed.1 store rich ∧
      framePeak ((runCachedPrefixWithTrace parsed.1 store rich).2.take steps) ≤
        cachedEnvelope frame parsed.1 store rich :=
  all_prefix _ _ (accepted_cached_usage frame parsed hParsed store rich) borrowed steps

theorem raw_all_prefix (rich : Bool) (frame seed : List Bool) (borrowed steps : ℕ) :
    retainedHeap (borrowed+frame.length+seed.length)
        (BinaryTerminalPhysicalFullRawLifetime.runWithTrace rich frame seed).2 steps ≤
        borrowed+frame.length+seed.length+rawEnvelope rich frame seed ∧
      framePeak ((BinaryTerminalPhysicalFullRawLifetime.runWithTrace
        rich frame seed).2.take steps) ≤ rawEnvelope rich frame seed :=
  all_prefix _ _ (raw_usage rich frame seed) (borrowed+frame.length+seed.length) steps

end Blotto.BinaryTerminalPhysicalReturnedSpace
