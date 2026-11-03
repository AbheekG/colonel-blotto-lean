import Blotto.BinaryFourParentCompiler
import Blotto.NativeBinarySegmentSampler
import Blotto.BinaryCategoricalFallback
import Blotto.WordMappedIndexedRefinement
import Blotto.WordMachineLowerLeaf
import Blotto.WordMachineRunEmbedding
import Blotto.RationalFourProgram
import Blotto.RationalFourBranchRun

/-! The gluing branch compiles its original six stored words into all 81 slots,
then executes native categorical selection, interpolation and exact syntactic
lower-leaf fallback. Only stored Boolean data and erased admissibility proofs
enter execution. Indexed runs retain the global reader/cap and consumed position.
Artificial zero-weight endpoints preserve budgets without an added box claim.
Whole-model time/storage contracts remain separate from these exact semantics. -/
namespace Blotto.BinaryGluingSampler
open MeasureTheory
open BinaryRationalNormalization BinaryRationalEncoding BinaryStoredOverlapEnvironment

-- Equality belongs to this branch exactly as in the original compiler guard.
def Admissible (input : BinaryFourParameters.Input) : Prop :=
  ∃ source : RationalFourInput, input.Refines source ∧ (1-source.p)*source.ell ≤ source.w

structure Prepared where
  table : Segment 4 81
  canonical : table.Canonical
  nonnegative : ∀ slot, 0 ≤ value (table.weight.read slot)

theorem descriptor_nonnegative (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input) :
    ∀ slot, 0 ≤ value ((BinaryFourParentCompiler.descriptor input).weight.read slot) := by
  obtain ⟨source,hr,hCase⟩ := hAd
  intro slot
  rw [(BinaryFourParentCompiler.descriptor_refines input source hC hr hCase).1 slot]
  exact (source.gluingDescriptor hCase).nonnegative slot

def prepare (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input) : Prepared :=
  ⟨BinaryFourParentCompiler.descriptor input,BinaryFourParentCompiler.descriptor_canonical input hC,
    descriptor_nonnegative input hC hAd⟩

theorem prepare_refines (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hAd : Admissible input) (hr : input.Refines source)
    (hCase : (1-source.p)*source.ell ≤ source.w) : (prepare input hC hAd).table.Refines (source.gluingDescriptor hCase) :=
  BinaryFourParentCompiler.descriptor_refines input source hC hr hCase

noncomputable def sourceRow (row : FixedArrayTable 4 SignedWord) : Fin 4 → ℚ := fun j => value (row.read j)

namespace Prepared

def selectIndexed (prepared : Prepared) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : Option (Fin 81) × ℕ :=
  BinaryCategoricalRun.runIndexed 0 N bits
    (.remaining (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative)) pos hpos

def runIndexed (prepared : Prepared) (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool)
    (pos : ℕ) (hpos : pos ≤ N) : Option (FixedArrayTable 4 SignedWord) × ℕ :=
  let selected := prepared.selectIndexed N bits pos hpos
  (selected.1.map (fun slot => BinarySegmentPoint.sample prepared.table slot K scalar),selected.2)

def fallback (prepared : Prepared) (K : ℕ) (scalar : Fin K → Bool) : FixedArrayTable 4 SignedWord :=
  BinarySegmentPoint.sample prepared.table
    (BinaryCategoricalFallback.segment prepared.table prepared.canonical prepared.nonnegative 0) K scalar

def fixedSample (prepared : Prepared) (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) : FixedArrayTable 4 SignedWord :=
  match (prepared.runIndexed K N scalar bits 0 (Nat.zero_le N)).1 with
  | some row => row
  | none => prepared.fallback K scalar

theorem selectIndexed_refines (prepared : Prepared) (source : RationalSegmentLottery 4 81)
    (hr : prepared.table.Refines source) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    prepared.selectIndexed N bits pos hpos = (categoricalMachine (0 : Fin 81)).runCursorIndexed N bits (.state source.start) pos hpos := by
  have he := BinarySegmentCategorical.selectIndexed_refines prepared.table source prepared.canonical hr 0 N bits pos hpos
  exact he

theorem runIndexed_refines (prepared : Prepared) (source : RationalSegmentLottery 4 81)
    (hr : prepared.table.Refines source) (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool)
    (pos : ℕ) (hpos : pos ≤ N) :
    ((prepared.runIndexed K N scalar bits pos hpos).1.map sourceRow,(prepared.runIndexed K N scalar bits pos hpos).2) =
      (source.machine 0 K scalar).runCursorIndexed N bits (.state source.start) pos hpos := by
  unfold runIndexed
  rw [prepared.selectIndexed_refines source hr]
  unfold RationalSegmentLottery.machine
  rw [WordMappedIndexedRefinement.indexed_refines]
  simp only [Option.map_map,Function.comp_def,WordMappedIndexedRefinement.mapResult]
  apply Prod.ext
  · apply congrArg (fun f => ((categoricalMachine (0 : Fin 81)).runCursorIndexed N bits (.state source.start) pos hpos).1.map f)
    funext slot j
    exact BinarySegmentPoint.sample_value prepared.table source prepared.canonical hr slot K scalar j
  · rfl

theorem fallback_value (prepared : Prepared) (source : RationalSegmentLottery 4 81)
    (hr : prepared.table.Refines source) (K : ℕ) (scalar : Fin K → Bool) (j : Fin 4) :
    value ((prepared.fallback K scalar).read j) = (source.machine 0 K scalar).chooseLeaf source.start j := by
  have he := BinarySegmentPoint.sample_value prepared.table source prepared.canonical hr
    (BinaryCategoricalFallback.segment prepared.table prepared.canonical prepared.nonnegative 0) K scalar j
  have hs := BinaryCategoricalFallback.segment_refines prepared.table source prepared.canonical prepared.nonnegative hr 0
  have hp := congrArg (fun slot => source.point K slot scalar j) hs
  have hLeaf := WordStateMachine.mapped_chooseLeaf (categoricalMachine (0 : Fin 81))
    (fun slot => source.point K slot scalar) source.start
  exact he.trans (hp.trans (congrFun hLeaf.symm j))

theorem fixedSample_value (prepared : Prepared) (source : RationalSegmentLottery 4 81)
    (hr : prepared.table.Refines source) (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (j : Fin 4) :
    value ((prepared.fixedSample K N scalar bits).read j) =
      (source.machine 0 K scalar).output N source.start ((source.machine 0 K scalar).chooseLeaf source.start) bits j := by
  have he := congrArg Prod.fst (prepared.runIndexed_refines source hr K N scalar bits 0 (Nat.zero_le N))
  change (prepared.runIndexed K N scalar bits 0 (Nat.zero_le N)).1.map sourceRow =
    ((source.machine 0 K scalar).runNumeric N source.start bits).1 at he
  rw [← WordStateMachine.run_eq_numeric] at he
  change (prepared.runIndexed K N scalar bits 0 (Nat.zero_le N)).1.map sourceRow =
    ((source.machine 0 K scalar).run N source.start bits).1 at he
  unfold fixedSample WordStateMachine.output
  cases hn : (prepared.runIndexed K N scalar bits 0 (Nat.zero_le N)).1 with
  | none =>
    rw [hn,Option.map_none] at he
    rw [← he]
    exact prepared.fallback_value source hr K scalar j
  | some row =>
    rw [hn,Option.map_some] at he
    rw [← he]
    rfl

theorem fixedSample_canonical (prepared : Prepared) (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) :
    ∀ j, CanonicalWord ((prepared.fixedSample K N scalar bits).read j) := by
  unfold fixedSample runIndexed
  dsimp only
  cases hs : (prepared.selectIndexed N bits 0 (Nat.zero_le N)).1 with
  | none => exact BinarySegmentPoint.sample_canonical prepared.table _ K scalar prepared.canonical
  | some slot => exact BinarySegmentPoint.sample_canonical prepared.table slot K scalar prepared.canonical

theorem indexed_position (prepared : Prepared) (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool)
    (pos : ℕ) (hpos : pos ≤ N) : pos ≤ (prepared.runIndexed K N scalar bits pos hpos).2 ∧
      (prepared.runIndexed K N scalar bits pos hpos).2 ≤ N :=
  BinaryCategoricalRun.runIndexed_position 0 N bits (.remaining (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative)) pos hpos

end Prepared

-- This is the exact retained global four-variable gluing embedding, including
-- the same scalar and the same absolute reader position.
theorem source_gluing_indexed (source : RationalFourInput) (hCase : (1-source.p)*source.ell ≤ source.w)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    (source.machine K outer scalar).runCursorIndexed N bits (.state (source.start K outer scalar)) pos hpos =
      (source.gluingMachine hCase K scalar).runCursorIndexed N bits (.state (source.gluingDescriptor hCase).start) pos hpos := by
  rw [source.machine_refines]
  unfold RationalFourInput.start
  rw [dite_eq_left hCase]
  exact WordStateMachine.embedding_runCursorIndexed (source.gluingMachine hCase K scalar)
    (source.machineReference K outer scalar) (FourSamplingState.gluing hCase) (fun _ => rfl) N bits (.state (source.gluingDescriptor hCase).start) pos hpos

theorem source_gluing_fallback (source : RationalFourInput) (hCase : (1-source.p)*source.ell ≤ source.w)
    (K : ℕ) (outer scalar : Fin K → Bool) :
    source.fallback K outer scalar = (source.gluingMachine hCase K scalar).chooseLeaf (source.gluingDescriptor hCase).start := by
  rw [RationalFourInput.fallback,WordStateMachine.chooseLeaf_eq_lowerLeaf]
  unfold RationalFourInput.start
  rw [dite_eq_left hCase,source.gluing_specification,← WordStateMachine.chooseLeaf_eq_lowerLeaf]

def fixedSample (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) : FixedArrayTable 4 SignedWord :=
  (prepare input hC hAd).fixedSample K N scalar bits

theorem fixedSample_value (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hAd : Admissible input) (hr : input.Refines source)
    (hCase : (1-source.p)*source.ell ≤ source.w) (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (j : Fin 4) :
    value ((fixedSample input hC hAd K N scalar bits).read j) = source.fixedSample K N outer scalar bits j := by
  have he := (prepare input hC hAd).fixedSample_value (source.gluingDescriptor hCase)
    (prepare_refines input source hC hAd hr hCase) K N scalar bits j
  unfold RationalFourInput.fixedSample WordStateMachine.output
  rw [WordStateMachine.run_eq_numeric,WordStateMachine.runNumeric,source_gluing_indexed source hCase K N outer scalar bits 0 (Nat.zero_le N),
    source_gluing_fallback source hCase K outer scalar]
  change value ((fixedSample input hC hAd K N scalar bits).read j) =
    ((source.gluingMachine hCase K scalar).runNumeric N (source.gluingDescriptor hCase).start bits).1.getD _ j
  rw [← WordStateMachine.run_eq_numeric]
  exact he

theorem fixedSample_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) :
    ∀ j, CanonicalWord ((fixedSample input hC hAd K N scalar bits).read j) :=
  (prepare input hC hAd).fixedSample_canonical K N scalar bits

theorem fixedSample_fullBudget (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hAd : Admissible input) (hr : input.Refines source)
    (hCase : (1-source.p)*source.ell ≤ source.w) (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    FullBudget (source.B : ℝ) (fun j => (value ((fixedSample input hC hAd K N scalar bits).read j) : ℝ)) := by
  have he : (fun j => (value ((fixedSample input hC hAd K N scalar bits).read j) : ℝ)) =
      (fun j => (source.fixedSample K N outer scalar bits j : ℝ)) := by
    funext j
    rw [fixedSample_value input source hC hAd hr hCase]
  rw [he]
  exact source.fixedSample_fullBudget K N outer scalar bits

def sample (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K : ℕ) (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) : FixedArrayTable 4 SignedWord :=
  let inner := firstBitBlock (RationalFourInput.innerBitBudget K) K bits
  fixedSample input hC hAd K (RationalFourInput.coinBitBudget K)
    (secondBitBlock (RationalFourInput.coinBitBudget K) K inner)
    (firstBitBlock (RationalFourInput.coinBitBudget K) K inner)

theorem sample_value (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hAd : Admissible input) (hr : input.Refines source)
    (hCase : (1-source.p)*source.ell ≤ source.w) (K : ℕ) (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) (j : Fin 4) :
    value ((sample input hC hAd K bits).read j) = source.sample K bits j :=
  fixedSample_value input source hC hAd hr hCase K _ _ _ _ j

theorem sample_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K : ℕ) (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) :
    ∀ j, CanonicalWord ((sample input hC hAd K bits).read j) := fixedSample_canonical input hC hAd K _ _ _

theorem sample_fullBudget (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hAd : Admissible input) (hr : input.Refines source)
    (hCase : (1-source.p)*source.ell ≤ source.w) (K : ℕ) (bits : Fin (RationalFourInput.sampleBitBudget K) → Bool) :
    FullBudget (source.B : ℝ) (fun j => (value ((sample input hC hAd K bits).read j) : ℝ)) := by
  have he : (fun j => (value ((sample input hC hAd K bits).read j) : ℝ)) = (fun j => (source.sample K bits j : ℝ)) := by
    funext j
    rw [sample_value input source hC hAd hr hCase]
  rw [he]
  exact source.sample_fullBudget K bits

noncomputable def sampleLaw (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input) (K : ℕ) : Mixed 4 :=
  (fairBitLaw (RationalFourInput.sampleBitBudget K)).map (fun bits j => (value ((sample input hC hAd K bits).read j) : ℝ))

theorem sampleLaw_eq (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hAd : Admissible input) (hr : input.Refines source)
    (hCase : (1-source.p)*source.ell ≤ source.w) (K : ℕ) : sampleLaw input hC hAd K=source.sampleLaw K := by
  unfold sampleLaw RationalFourInput.sampleLaw
  congr 1
  funext bits j
  rw [sample_value input source hC hAd hr hCase]

theorem sampleLaw_CDF_error (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hAd : Admissible input) (hr : input.Refines source)
    (hCase : (1-source.p)*source.ell ≤ source.w) (K : ℕ) :
    CDFClose (sampleLaw input hC hAd K) source.real.law (5/(2*(2:ℝ)^K)) := by
  rw [sampleLaw_eq input source hC hAd hr hCase]
  exact source.sampleLaw_CDF_error K

end Blotto.BinaryGluingSampler
