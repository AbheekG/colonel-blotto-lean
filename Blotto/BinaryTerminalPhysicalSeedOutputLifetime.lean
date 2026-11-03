import Blotto.BinaryTerminalPhysicalFramedLifetime
import Blotto.BinaryPRGHeapSeedOutputLifetime
import Blotto.BinaryPRGSeedOutputLifetimePolynomial

/-! Accepted physical requests retain their terminal stores through validated
seed tapes, seed-store preparation and framed output. Rejected seeds never
enter the draw. -/
namespace Blotto.BinaryTerminalPhysicalSeedOutputLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage RationalLottoResourceSystem
set_option maxHeartbeats 3000000

private abbrev PhysicalParsed :=
  (Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n) × List Bool

def outputWithTrace (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool)
    (blocks : BinaryPRGTapeSeedBlocks.Blocks parsed.1.1
      parsed.1.2.logical.request.precision) : List Bool × Trace :=
  let seedStore := BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits
  let output := BinaryTerminalPhysicalFramedLifetime.runWithTrace
    frame parsed hParsed seedStore.1 rich parsed.1.2.logical.request.precision
    blocks.outer blocks.scalar parsed.1.2.logical.header
  (output.1.1,wrap 16 2 [seedStore.2,output.2])

theorem output_state (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool)
    (blocks : BinaryPRGTapeSeedBlocks.Blocks parsed.1.1
      parsed.1.2.logical.request.precision) :
    (outputWithTrace frame parsed hParsed rich blocks).1 =
      (BinaryPRGTapeSeedOutputLifetime.outputWithTrace
        parsed.1.2.logical rich blocks).1 := by
  simp only [outputWithTrace,BinaryPRGTapeSeedOutputLifetime.outputWithTrace,
    BinaryTerminalPhysicalFramedLifetime.accepted_output]

theorem output_original (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool)
    (blocks : BinaryPRGTapeSeedBlocks.Blocks parsed.1.1
      parsed.1.2.logical.request.precision) :
    (outputWithTrace frame parsed hParsed rich blocks).1 =
      (BinaryPRGSeedBlockOutput.output parsed.1.2.logical rich blocks.erase).1 := by
  rw [output_state,BinaryPRGTapeSeedOutputLifetime.output_original]

noncomputable def outputEnvelope (frame : List Bool)
    (parsed : Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n)
    (blocks : BinaryPRGTapeSeedBlocks.Blocks parsed.1
      parsed.2.logical.request.precision) : ℕ :=
  let store := BinarySeedLookupTree.prepare blocks.choice.bits
  BinaryTerminalPhysicalFramedLifetime.envelope frame parsed store
    parsed.2.logical.request.precision parsed.2.logical.header.bytes.length+
    49*blocks.choice.bits.length+80

theorem output_usage_additive (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool)
    (blocks : BinaryPRGTapeSeedBlocks.Blocks parsed.1.1
      parsed.1.2.logical.request.precision) :
    usage (outputWithTrace frame parsed hParsed rich blocks).2 ≤
      usage (BinaryTerminalPhysicalFramedLifetime.runWithTrace
        frame parsed hParsed
        (BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits).1 rich
        parsed.1.2.logical.request.precision blocks.outer blocks.scalar
        parsed.1.2.logical.header).2+
      49*blocks.choice.bits.length+80 := by
  let seed := blocks.choice.bits
  let store := BinaryWordStoreLifetime.prepareWithTrace seed
  let output := BinaryTerminalPhysicalFramedLifetime.runWithTrace
    frame parsed hParsed store.1 rich parsed.1.2.logical.request.precision
    blocks.outer blocks.scalar parsed.1.2.logical.header
  have hStore := BinaryWordStoreLifetime.prepareWithTrace_bounds seed
  have hStoreUsage : usage store.2 ≤ 49*seed.length+33 := by
    change listCells store.2+arraySlots store.2 ≤ 46*seed.length+20 ∧
      framePeak store.2 ≤ 2*seed.length+binaryWordWidth seed.length+12 at hStore
    have hLog := Nat.log2_le_self seed.length
    have hWidth : binaryWordWidth seed.length ≤ seed.length+1 := by
      unfold binaryWordWidth
      omega
    unfold usage BinaryPRGHeapPrimitiveLifetime.cells
    omega
  have hw := wrap_usage 16 2 [store.2,output.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (outputWithTrace frame parsed hParsed rich blocks).2 ≤ _ at hw
  dsimp only [seed] at hStoreUsage
  change usage (outputWithTrace frame parsed hParsed rich blocks).2 ≤
    usage output.2+49*blocks.choice.bits.length+80
  omega

theorem output_usage (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool)
    (blocks : BinaryPRGTapeSeedBlocks.Blocks parsed.1.1
      parsed.1.2.logical.request.precision) :
    usage (outputWithTrace frame parsed hParsed rich blocks).2 ≤
      outputEnvelope frame parsed.1 blocks := by
  have hAdd := output_usage_additive frame parsed hParsed rich blocks
  have hOut := BinaryTerminalPhysicalFramedLifetime.accepted_usage
    frame parsed hParsed
    (BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits).1 rich
    parsed.1.2.logical.request.precision blocks.outer blocks.scalar
    parsed.1.2.logical.header
  have hE := BinaryWordStoreLifetime.prepareWithTrace_erases blocks.choice.bits
  dsimp only [outputEnvelope]
  rw [← hE]
  omega

theorem accepted_output_uniform_polynomial :
    ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : PhysicalParsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (rich : Bool)
      (blocks : BinaryPRGTapeSeedBlocks.Blocks parsed.1.1
        parsed.1.2.logical.request.precision),
      usage (outputWithTrace frame parsed hParsed rich blocks).2 ≤
        C*(frame.length+1)^d := by
  obtain ⟨C,d,hFramed⟩ :=
    BinaryTerminalPhysicalFramedLifetime.accepted_uniform_polynomial
  refine ⟨C*20000^d+150000,d+1,?_⟩
  intro frame parsed hParsed rich blocks
  let K := parsed.1.2.logical.request.precision
  let N := blocks.choice.bits.length
  let store := BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits
  let X := frame.length+1
  have hX : 0 < X := by dsimp only [X]; omega
  have hOld := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_original frame
  rw [hParsed] at hOld
  have hAcc : (BinaryPRGAccuracyRulerRequest.read frame).1 =
      some (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) := by
    simpa only [Option.map_some] using hOld.symm
  have hn := BinaryTerminalPhysicalRouteLifetime.accepted_dimension
    frame parsed hParsed
  have hK := BinaryPRGAccuracyRulerRequest.read_precision_bound
    frame (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) hAcc
  change K ≤ frame.length+5 at hK
  have hSeed := BinaryPRGSeedRequestBound.read_seedCount_bound
    frame (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) hAcc
  have hN : N ≤ 8*frame.length+3025 := by
    have hChoice := blocks.choice.size
    change N = coinBitBudget parsed.1.1 K at hChoice
    change sampleBitBudget parsed.1.1 K ≤
      BinaryPRGSeedRequestBound.seedCountBound frame.length at hSeed
    unfold sampleBitBudget innerBitBudget
      BinaryPRGSeedRequestBound.seedCountBound at hSeed
    omega
  have hHeader := BinaryPRGSeedOutputLifetimePolynomial.header_length
    parsed.1.2.logical.header
  have hE : store.1 = BinarySeedLookupTree.prepare blocks.choice.bits :=
    BinaryWordStoreLifetime.prepareWithTrace_erases blocks.choice.bits
  have hStoreWidth : store.1.width ≤ N+1 := by
    rw [hE]
    exact (BinarySeedLookupTree.prepare_width_bound blocks.choice.bits).trans
      (BinaryPRGSeedOutputLifetimePolynomial.wordWidth_le N)
  have hStoreCap : store.1.cap.value = N := by
    rw [hE,BinarySeedLookupTree.prepare_cap]
  have hSize : frame.length+K+store.1.width+store.1.cap.value+
      parsed.1.2.logical.header.bytes.length+3 ≤ 20000*X := by
    dsimp only [K,N,X] at *
    omega
  have hOut := hFramed frame parsed hParsed store.1 rich K
    blocks.outer blocks.scalar parsed.1.2.logical.header
  have hFramedTop : usage (BinaryTerminalPhysicalFramedLifetime.runWithTrace
      frame parsed hParsed store.1 rich K blocks.outer blocks.scalar
      parsed.1.2.logical.header).2 ≤ C*20000^d*X^d := by
    have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hSize d)
    rw [Nat.mul_pow] at hp
    exact hOut.trans (hp.trans_eq (by ring))
  have hAdd := output_usage_additive frame parsed hParsed rich blocks
  have hLinear : 49*N+80 ≤ 150000*X := by
    dsimp only [N,X] at *
    omega
  have hPow : X^d ≤ X^(d+1) :=
    Nat.pow_le_pow_right hX (by omega)
  have hXPower : X ≤ X^(d+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hX
      (show 1 ≤ d+1 by omega)
  have hScaled := Nat.mul_le_mul_left (C*20000^d) hPow
  have hLinearScaled := Nat.mul_le_mul_left 150000 hXPower
  change usage (outputWithTrace frame parsed hParsed rich blocks).2 ≤
    (C*20000^d+150000)*X^(d+1)
  nlinarith only [hAdd,hFramedTop,hLinear,hScaled,hLinearScaled]

def runWithTrace (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) : Option (List Bool) × Trace :=
  let blocks := BinaryPRGBooleanSeedBlocks.readWithTrace parsed.1.2.logical seed
  match blocks.1 with
  | none => (none,wrap 16 2 [blocks.2])
  | some tapes =>
      let output := outputWithTrace frame parsed hParsed rich tapes
      (some output.1,wrap 32 2 [blocks.2,output.2])

theorem accepted_state (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (runWithTrace frame parsed hParsed rich seed).1 =
      (BinaryPRGHeapSeedOutputLifetime.runWithTrace
        parsed.1.2.logical rich seed).1 := by
  cases h : (BinaryPRGBooleanSeedBlocks.readWithTrace
      parsed.1.2.logical seed).1 with
  | none => simp only [runWithTrace,BinaryPRGHeapSeedOutputLifetime.runWithTrace,h]
  | some tapes =>
      simp only [runWithTrace,BinaryPRGHeapSeedOutputLifetime.runWithTrace,
        h,output_state frame parsed hParsed rich tapes]

theorem accepted_request (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (runWithTrace frame parsed hParsed rich seed).1 =
      (RationalPRGBinaryRequest.seedTable
        (sampleBitBudget parsed.1.1 parsed.1.2.logical.request.precision) seed).map
        (fun table => parsed.1.2.logical.request.output rich table.read) := by
  rw [accepted_state]
  exact BinaryPRGHeapSeedOutputLifetime.runWithTrace_request
    parsed.1.2.logical rich seed

theorem accepted_reject (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    (runWithTrace frame parsed hParsed rich seed).1 = none ↔
      (BinaryPRGSeedBlocks.read parsed.1.1
        parsed.1.2.logical.request.precision seed).1 = none := by
  rw [accepted_state]
  exact BinaryPRGHeapSeedOutputLifetime.runWithTrace_reject
    parsed.1.2.logical rich seed

theorem accepted_read (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed bytes : List Bool)
    (h : (runWithTrace frame parsed hParsed rich seed).1 = some bytes) :
    ∃ tables : BinaryPRGSeedBlocks.Tables parsed.1.1
        parsed.1.2.logical.request.precision,
      (BinaryPRGSeedBlocks.read parsed.1.1
        parsed.1.2.logical.request.precision seed).1 = some tables ∧
      tables.flatList = seed ∧ ∀ suffix,
        BinaryRatListFrame.readRow (bytes++suffix) =
          some (parsed.1.1,List.ofFn (if rich then
            parsed.1.2.logical.request.source.richSample
              parsed.1.2.logical.request.precision tables.flat
            else parsed.1.2.logical.request.source.poorSample
              parsed.1.2.logical.request.precision tables.flat),suffix) := by
  rw [accepted_state] at h
  exact BinaryPRGHeapSeedOutputLifetime.runWithTrace_read
    parsed.1.2.logical rich seed bytes h

theorem accepted_budget (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed bytes : List Bool)
    (h : (runWithTrace frame parsed hParsed rich seed).1 = some bytes) :
    RationalPRGBinaryRequest.ReturnedBudget parsed.1.1
      (if rich then parsed.1.2.logical.request.source.a
        else parsed.1.2.logical.request.source.b) bytes := by
  rw [accepted_state] at h
  exact BinaryPRGHeapSeedOutputLifetime.runWithTrace_budget
    parsed.1.2.logical rich seed bytes h

noncomputable def envelope (frame : List Bool)
    (parsed : Σ n, BinaryPRGPhysicalRawRequestLifetime.Request n)
    (seed : List Bool) : ℕ :=
  BinaryPRGHeapSeedOutputLifetime.preparationEnvelope
    parsed.1 parsed.2.logical.request.precision+
  ((BinaryPRGTapeSeedBlocks.readWithTrace parsed.1
    parsed.2.logical.request.precision seed).1.map
      (outputEnvelope frame parsed)).getD 0+128

theorem accepted_usage (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) :
    usage (runWithTrace frame parsed hParsed rich seed).2 ≤
      envelope frame parsed.1 seed := by
  let blocks := BinaryPRGTapeSeedBlocks.readWithTrace parsed.1.1
    parsed.1.2.logical.request.precision seed
  have hPrep := BinaryPRGTapeSeedBlocks.read_usage parsed.1.1
    parsed.1.2.logical.request.precision seed
  change usage blocks.2 ≤ BinaryPRGHeapSeedOutputLifetime.preparationEnvelope
    parsed.1.1 parsed.1.2.logical.request.precision at hPrep
  unfold runWithTrace
  rw [BinaryPRGBooleanSeedBlocks.read_same]
  dsimp only
  split
  · rename_i hNone
    have hw := wrap_usage 16 2 [blocks.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 16 2 [blocks.2]) ≤ _
    unfold envelope
    rw [hNone]
    simp only [Option.map_none,Option.getD_none]
    omega
  · rename_i tapes hSome
    have hOut := output_usage frame parsed hParsed rich tapes
    have hw := wrap_usage 32 2
      [blocks.2,(outputWithTrace frame parsed hParsed rich tapes).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 32 2
      [blocks.2,(outputWithTrace frame parsed hParsed rich tapes).2]) ≤ _
    unfold envelope
    rw [hSome]
    simp only [Option.map_some,Option.getD_some]
    omega

theorem accepted_preparation_polynomial (frame : List Bool)
    (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) :
    BinaryPRGHeapSeedOutputLifetime.preparationEnvelope parsed.1.1
      parsed.1.2.logical.request.precision ≤
        10000000*(frame.length+1)^2 := by
  let S := sampleBitBudget parsed.1.1 parsed.1.2.logical.request.precision
  let X := frame.length+1
  have hOld := BinaryPRGPhysicalRawRequestLifetime.readWithTrace_original frame
  rw [hParsed] at hOld
  have hAcc : (BinaryPRGAccuracyRulerRequest.read frame).1 =
      some (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) := by
    simpa only [Option.map_some] using hOld.symm
  have hSeed := BinaryPRGSeedRequestBound.read_seedCount_bound
    frame (BinaryPRGPhysicalRawRequestLifetime.forgetParsed parsed) hAcc
  change S ≤ BinaryPRGSeedRequestBound.seedCountBound frame.length at hSeed
  have hS : S ≤ 3033*X := by
    unfold BinaryPRGSeedRequestBound.seedCountBound at hSeed
    dsimp only [X]
    omega
  have hSquare := Nat.pow_le_pow_left hS 2
  rw [Nat.mul_pow] at hSquare
  have hX : 0 < X := by dsimp only [X]; omega
  have hXsq : X ≤ X^2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hX (by decide : 1 ≤ 2)
  have hOne : 1 ≤ X^2 := Nat.one_le_pow 2 X (by omega)
  change ownedBound S+2*S+10 ≤ 10000000*X^2
  unfold ownedBound
  nlinarith only [hSquare,hS,hXsq,hOne]

theorem accepted_uniform_polynomial :
    ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : PhysicalParsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (rich : Bool) (seed : List Bool),
      usage (runWithTrace frame parsed hParsed rich seed).2 ≤
        C*(frame.length+1)^d := by
  obtain ⟨C,d,hOutput⟩ := accepted_output_uniform_polynomial
  refine ⟨C+10000000+128,max d 2,?_⟩
  intro frame parsed hParsed rich seed
  let X := frame.length+1
  let D := max d 2
  have hX : 0 < X := by dsimp only [X]; omega
  have hPrep := accepted_preparation_polynomial frame parsed hParsed
  have hBlocks := BinaryPRGTapeSeedBlocks.read_usage parsed.1.1
    parsed.1.2.logical.request.precision seed
  have hPrepTrace : usage (BinaryPRGTapeSeedBlocks.readWithTrace
      parsed.1.1 parsed.1.2.logical.request.precision seed).2 ≤
      10000000*X^2 := hBlocks.trans hPrep
  have hd : X^d ≤ X^D :=
    Nat.pow_le_pow_right hX (Nat.le_max_left d 2)
  have h2 : X^2 ≤ X^D :=
    Nat.pow_le_pow_right hX (Nat.le_max_right d 2)
  have hOne : 1 ≤ X^D := Nat.one_le_pow D X (by omega)
  have hPrepTop := Nat.mul_le_mul_left 10000000 h2
  have hOutputTop := Nat.mul_le_mul_left C hd
  unfold runWithTrace
  rw [BinaryPRGBooleanSeedBlocks.read_same]
  dsimp only
  split
  · have hw := wrap_usage 16 2
      [(BinaryPRGTapeSeedBlocks.readWithTrace parsed.1.1
        parsed.1.2.logical.request.precision seed).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 16 2
      [(BinaryPRGTapeSeedBlocks.readWithTrace parsed.1.1
        parsed.1.2.logical.request.precision seed).2]) ≤ _
    change _ ≤ (C+10000000+128)*X^D
    nlinarith only [hw,hPrepTrace,hPrepTop,hOne]
  · rename_i tapes hSome
    have hOut := hOutput frame parsed hParsed rich tapes
    change usage (outputWithTrace frame parsed hParsed rich tapes).2 ≤
      C*X^d at hOut
    have hw := wrap_usage 32 2
      [(BinaryPRGTapeSeedBlocks.readWithTrace parsed.1.1
        parsed.1.2.logical.request.precision seed).2,
        (outputWithTrace frame parsed hParsed rich tapes).2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change usage (wrap 32 2
      [(BinaryPRGTapeSeedBlocks.readWithTrace parsed.1.1
        parsed.1.2.logical.request.precision seed).2,
        (outputWithTrace frame parsed hParsed rich tapes).2]) ≤ _
    change _ ≤ (C+10000000+128)*X^D
    nlinarith only [hw,hPrepTrace,hPrepTop,hOut,hOutputTop,hOne]

theorem accepted_uniform_all_prefix :
    ∃ C d : ℕ, ∀ (frame : List Bool) (parsed : PhysicalParsed)
      (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
      (rich : Bool) (seed : List Bool) (borrowed steps : ℕ),
      retainedHeap (borrowed+seed.length)
          (runWithTrace frame parsed hParsed rich seed).2 steps ≤
          borrowed+seed.length+C*(frame.length+1)^d ∧
        framePeak ((runWithTrace frame parsed hParsed rich seed).2.take steps) ≤
          C*(frame.length+1)^d := by
  obtain ⟨C,d,hUsage⟩ := accepted_uniform_polynomial
  exact ⟨C,d,fun frame parsed hParsed rich seed borrowed steps =>
    BinaryPRGHeapTraceUsage.all_prefix _ _
      (hUsage frame parsed hParsed rich seed) _ steps⟩

theorem accepted_all_prefix (frame : List Bool) (parsed : PhysicalParsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed)
    (rich : Bool) (seed : List Bool) (borrowed steps : ℕ) :
    retainedHeap (borrowed+seed.length)
        (runWithTrace frame parsed hParsed rich seed).2 steps ≤
        borrowed+seed.length+envelope frame parsed.1 seed ∧
      framePeak ((runWithTrace frame parsed hParsed rich seed).2.take steps) ≤
        envelope frame parsed.1 seed :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (accepted_usage frame parsed hParsed rich seed) _ steps

end Blotto.BinaryTerminalPhysicalSeedOutputLifetime
