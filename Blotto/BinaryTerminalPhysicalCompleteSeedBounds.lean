import Blotto.BinaryTerminalPhysicalCompleteSeedMeasured

/-! Actual validated tape/store sizes instantiate the complete framer bounds.
Validation, choice-store preparation, reached terminal/fallback/output and all
retained trace prefixes have frame-only polynomial source bounds, uniformly
over supplied seeds, including rejected or overlong seeds. -/
namespace Blotto.BinaryTerminalPhysicalCompleteSeedBounds
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTerminalPhysicalAllowanceCache (Parsed)
open BinaryTerminalPhysicalCompleteSeedMeasured
set_option autoImplicit false
set_option maxHeartbeats 2000000

-- Keep the complete framed record behind its public contracts while reducing
-- the seed wrapper; projected charge metadata need not be evaluated here.
attribute [local irreducible] BinaryTerminalPhysicalCompleteFramedMeasured.run

theorem framed_joint : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (rich : Bool)
    (blocks : BinaryPRGTapeSeedBlocks.Blocks parsed.1.1 parsed.1.2.logical.request.precision),
    let drawn := BinaryTerminalPhysicalCompleteFramedMeasured.run frame parsed hParsed
      (BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits).1 rich parsed.1.2.logical.request.precision
      blocks.outer blocks.scalar parsed.1.2.logical.header
    drawn.2+BinaryBigEndian.littleValue drawn.1.1.2+usage drawn.1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hBound⟩ := BinaryTerminalPhysicalCompleteFramedMeasured.accepted_uniform_joint
  refine ⟨C*20000^d,d,?_⟩
  intro frame parsed hParsed rich blocks
  have h := hBound frame parsed hParsed (BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits).1 rich
    parsed.1.2.logical.request.precision blocks.outer blocks.scalar parsed.1.2.logical.header
  have hp := Nat.mul_le_mul_left C (Nat.pow_le_pow_left (store_parameters frame parsed hParsed blocks) d)
  rw [Nat.mul_pow] at hp
  exact h.trans (hp.trans_eq (by ring))

theorem accepted_uniform_joint : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (rich : Bool) (seed : List Bool),
    (run frame parsed hParsed rich seed).2+BinaryBigEndian.littleValue (run frame parsed hParsed rich seed).1.1.2+
      usage (run frame parsed hParsed rich seed).1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,hFramed⟩ := framed_joint
  let D := max d 2
  refine ⟨C+12000000,D,?_⟩
  intro frame parsed hParsed rich seed
  let prepared := BinarySeedPreparationMeasured.prepare parsed.1.2.logical seed
  let X := frame.length+1
  have hX : 0 < X := by dsimp only [X]; omega
  have hPW := BinaryTerminalPhysicalPreparationWork.preparation_frame_bound frame parsed hParsed seed
  have hPU := preparation_usage frame parsed hParsed seed
  change prepared.2 ≤ 128000*X at hPW
  change usage prepared.1.2 ≤ 10000000*X^2 at hPU
  have hd := Nat.mul_le_mul_left C (Nat.pow_le_pow_right hX (Nat.le_max_left d 2))
  change C*X^d ≤ C*X^D at hd
  have hLinear : X ≤ X^D := by
    simpa only [pow_one] using Nat.pow_le_pow_right hX (show 1 ≤ D by dsimp only [D]; omega)
  have hSquare : X^2 ≤ X^D := Nat.pow_le_pow_right hX (Nat.le_max_right d 2)
  have hOne : 1 ≤ X^D := Nat.one_le_pow _ _ (by omega)
  rw [run_eq_reference]
  unfold runReference
  dsimp only
  split
  · have hw := wrap_usage 16 2 [prepared.1.2]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
    change prepared.2+4+0+usage (wrap 16 2 [prepared.1.2]) ≤ (C+12000000)*X^D
    calc
      _ ≤ C*X^D+12000000*X^D := by omega
      _ = _ := by ring
  · rename_i held hPrepared
    obtain ⟨blocks,hHeld⟩ := prepared_some parsed.1.2.logical seed held hPrepared
    subst held
    let drawn := BinaryTerminalPhysicalCompleteFramedMeasured.run frame parsed hParsed
      (BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits).1 rich parsed.1.2.logical.request.precision
      blocks.outer blocks.scalar parsed.1.2.logical.header
    have hF := hFramed frame parsed hParsed rich blocks
    change drawn.2+BinaryBigEndian.littleValue drawn.1.1.2+usage drawn.1.2 ≤ C*X^d at hF
    have hS := store_usage frame parsed hParsed blocks
    change usage (BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits).2 ≤ 500000*X at hS
    have hi := wrap_usage 16 2 [(BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits).2,drawn.1.2]
    have ho := wrap_usage 32 2 [prepared.1.2,wrap 16 2 [(BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits).2,drawn.1.2]]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hi ho
    change prepared.2+drawn.2+8+BinaryBigEndian.littleValue drawn.1.1.2+
      usage (wrap 32 2 [prepared.1.2,wrap 16 2 [(BinaryWordStoreLifetime.prepareWithTrace blocks.choice.bits).2,drawn.1.2]]) ≤
        (C+12000000)*X^D
    calc
      _ ≤ C*X^D+12000000*X^D := by omega
      _ = _ := by ring

theorem accepted_uniform_work : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (rich : Bool) (seed : List Bool),
    (run frame parsed hParsed rich seed).2+BinaryBigEndian.littleValue (run frame parsed hParsed rich seed).1.1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,h⟩ := accepted_uniform_joint
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed rich seed
  have hb := h frame parsed hParsed rich seed
  omega

theorem accepted_uniform_usage : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (rich : Bool) (seed : List Bool),
    usage (run frame parsed hParsed rich seed).1.2 ≤ C*(frame.length+1)^d := by
  obtain ⟨C,d,h⟩ := accepted_uniform_joint
  refine ⟨C,d,?_⟩
  intro frame parsed hParsed rich seed
  have hb := h frame parsed hParsed rich seed
  omega

theorem accepted_all_prefix : ∃ C d : ℕ,∀ (frame : List Bool) (parsed : Parsed)
    (hParsed : (BinaryPRGPhysicalRawRequestLifetime.readWithTrace frame).1 = some parsed) (rich : Bool) (seed : List Bool) (borrowed steps : ℕ),
    let B := C*(frame.length+1)^d
    retainedHeap (borrowed+frame.length+seed.length) (run frame parsed hParsed rich seed).1.2 steps ≤
      borrowed+frame.length+seed.length+B ∧ framePeak ((run frame parsed hParsed rich seed).1.2.take steps) ≤ B := by
  obtain ⟨C,d,h⟩ := accepted_uniform_usage
  exact ⟨C,d,fun frame parsed hParsed rich seed borrowed steps =>
    all_prefix _ _ (h frame parsed hParsed rich seed) (borrowed+frame.length+seed.length) steps⟩

end Blotto.BinaryTerminalPhysicalCompleteSeedBounds
