import Blotto.BinaryStoredSegmentFixedWork
import Blotto.BinaryCachedFourParameterWork
import Blotto.RationalFourGluingHeight
import Blotto.BinaryFourPartialRun

/-! The actual 81-slot four-variable gluing sampler joins descriptor,
categorical, interpolation and exact lower-leaf fallback primitive work.
Source heights derive every stored weight/endpoint width. Equality remains in
the original gluing guard; none and absolute positions refine the old runner.
Sorting/restoration, reflected continuation and model metadata remain separate. -/

namespace Blotto.BinaryGluingDrawWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryGluingSampler

def asSegment (prepared : Prepared) : BinaryStoredSegmentProgram.Prepared 4 81 :=
  ⟨prepared.table, prepared.canonical, prepared.nonnegative⟩

def runIndexedWithWork (prepared : Prepared) (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool)
    (pos : ℕ) (hp : pos ≤ N) : (Option (FixedArrayTable 4 SignedWord) × ℕ) × ℕ :=
  BinaryStoredSegmentDrawWork.runIndexedWork (asSegment prepared) 0 K N scalar bits pos hp

theorem runIndexedWithWork_state (prepared : Prepared) (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool)
    (pos : ℕ) (hp : pos ≤ N) :
    (runIndexedWithWork prepared K N scalar bits pos hp).1 = prepared.runIndexed K N scalar bits pos hp :=
  BinaryStoredSegmentDrawWork.runIndexedWork_state (asSegment prepared) 0 K N scalar bits pos hp

def fixedSampleWithWork (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) : FixedArrayTable 4 SignedWord × ℕ :=
  let prepared := prepare input hC hAd
  let drawn := BinaryStoredSegmentFixedWork.sampleWithWork (asSegment prepared) 0 K N scalar bits
  (drawn.1, BinaryFourParentCompiler.descriptorWork input + drawn.2)

theorem asSegment_sample_state (prepared : Prepared) (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (asSegment prepared).sample 0 K N scalar bits = prepared.fixedSample K N scalar bits := by
  have hRun := (BinaryStoredSegmentDrawWork.runIndexedWork_state (asSegment prepared) 0 K N scalar bits 0 (Nat.zero_le N)).symm.trans
    (runIndexedWithWork_state prepared K N scalar bits 0 (Nat.zero_le N))
  unfold BinaryStoredSegmentProgram.Prepared.sample Prepared.fixedSample
  rw [hRun]
  cases hs : (prepared.runIndexed K N scalar bits 0 (Nat.zero_le N)).1 <;> rfl

theorem fixedSampleWithWork_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (fixedSampleWithWork input hC hAd K N scalar bits).1 = BinaryGluingSampler.fixedSample input hC hAd K N scalar bits := by
  exact (BinaryStoredSegmentFixedWork.sampleWithWork_state (asSegment (prepare input hC hAd)) 0 K N scalar bits).trans
    (asSegment_sample_state (prepare input hC hAd) K N scalar bits)

def bound (s K N : ℕ) : ℕ := BinaryFourParentCompiler.workBound s +
  BinaryStoredSegmentFixedWork.bound 4 81 (expressionHeightBudget s 36) (expressionHeightBudget s 36) K N

theorem fixedSampleWithWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : Admissible input)
    (hCase : (1 - source.p) * source.ell ≤ source.w) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (fixedSampleWithWork input hC hAd K N scalar bits).2 ≤ bound s K N := by
  have hTable := prepare_refines input source hC hAd hR hCase
  have hHeight := hH.gluingDescriptor hs hCase
  have hDescriptor := BinaryFourParentCompiler.descriptorWork_bound input source hC hR hCase s hs hH
  have hDraw := BinaryStoredSegmentFixedWork.sampleWithWork_bound (asSegment (prepare input hC hAd))
    (source.gluingDescriptor hCase) hTable (expressionHeightBudget s 36) (expressionHeightBudget s 36)
    (hs.trans (expressionHeightBudget_ge_input s 36)) hHeight.1 hHeight.2 0 K N scalar bits
  exact Nat.add_le_add hDescriptor hDraw

def partialWithWork (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (Option (FixedArrayTable 4 SignedWord) × ℕ) × ℕ :=
  let prepared := prepare input hC hAd
  let drawn := runIndexedWithWork prepared K N scalar bits pos hp
  (drawn.1, BinaryFourParentCompiler.descriptorWork input + drawn.2)

theorem partialWithWork_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (partialWithWork input hC hAd K N scalar bits pos hp).1 =
      (prepare input hC hAd).runIndexed K N scalar bits pos hp :=
  runIndexedWithWork_state (prepare input hC hAd) K N scalar bits pos hp

def partialBound (s K remaining : ℕ) : ℕ := BinaryFourParentCompiler.workBound s +
  BinaryStoredSegmentChoiceWork.selectionBound 81 (expressionHeightBudget s 36) remaining +
    BinaryStoredSegmentDrawWork.pointBound 4 (expressionHeightBudget s 36) K

theorem partialWithWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : Admissible input)
    (hCase : (1 - source.p) * source.ell ≤ source.w) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (partialWithWork input hC hAd K N scalar bits pos hp).2 ≤ partialBound s K (N - pos) := by
  have hTable := prepare_refines input source hC hAd hR hCase
  have hHeight := hH.gluingDescriptor hs hCase
  have hDescriptor := BinaryFourParentCompiler.descriptorWork_bound input source hC hR hCase s hs hH
  have hDraw := BinaryStoredSegmentDrawWork.runIndexedWork_bound (asSegment (prepare input hC hAd))
    (source.gluingDescriptor hCase) hTable (expressionHeightBudget s 36) (expressionHeightBudget s 36)
    (hs.trans (expressionHeightBudget_ge_input s 36)) hHeight.1 hHeight.2 0 K N scalar bits pos hp
  exact (Nat.add_le_add hDescriptor hDraw).trans_eq (by unfold partialBound; omega)

theorem selectIndexed_window (prepared : Prepared) (source : RationalSegmentLottery 4 81)
    (hR : prepared.table.Refines source) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    prepared.selectIndexed N bits pos hp =
      let result := prepared.selectIndexed (N - pos) (WordStateMachine.inputWindow bits pos (N - pos) (by omega))
        0 (Nat.zero_le (N - pos))
      (result.1, pos + result.2) := by
  rw [prepared.selectIndexed_refines source hR, prepared.selectIndexed_refines source hR]
  rw [(categoricalMachine (0 : Fin 81)).runCursorIndexed_window N bits (.state source.start) pos (N - pos) (by omega)]
  rw [(categoricalMachine (0 : Fin 81)).runCursorIndexed_zero]
  rfl

theorem runIndexed_window (prepared : Prepared) (source : RationalSegmentLottery 4 81)
    (hR : prepared.table.Refines source) (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    prepared.runIndexed K N scalar bits pos hp =
      let result := prepared.runIndexed K (N - pos) scalar (WordStateMachine.inputWindow bits pos (N - pos) (by omega))
        0 (Nat.zero_le (N - pos))
      (result.1, pos + result.2) := by
  unfold Prepared.runIndexed
  rw [selectIndexed_window prepared source hR N bits pos hp]

theorem partialWithWork_native (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : BinaryFourAdmissibility.Admissible input)
    (hGuard : BinaryFourParentCompiler.gluingCase input = true)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (partialWithWork input hC (BinaryFourAdmissibility.gluing_guard input hC hAd hGuard) K N scalar bits pos hp).1 =
      BinaryFourPartialRun.runIndexed input hC hAd K N outer scalar bits pos hp := by
  have hCase := (BinaryFourParentCompiler.gluingCase_iff input source hC hR).mp hGuard
  apply (partialWithWork_state input hC (BinaryFourAdmissibility.gluing_guard input hC hAd hGuard) K N scalar bits pos hp).trans
  have hTable := prepare_refines input source hC (BinaryFourAdmissibility.gluing_guard input hC hAd hGuard) hR hCase
  rw [runIndexed_window _ (source.gluingDescriptor hCase) hTable]
  unfold BinaryFourPartialRun.runIndexed BinaryFourPartialRun.run
  rw [dite_eq_left hGuard]

end Blotto.BinaryGluingDrawWork
