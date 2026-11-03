import Blotto.BinaryFourSampler
import Blotto.WordMappedIndexedRefinement

/-! Partial native four execution preserves exhaustion and absolute reader
positions. Fallback is left to the caller for general serial PRG composition.
The same branch/descriptor/root producers supply the actual stored outputs. -/

namespace Blotto.BinaryFourPartialRun
open BinaryRationalNormalization BinaryRationalEncoding BinaryFourAdmissibility

noncomputable def sourceRow (row : FixedArrayTable 4 SignedWord) : Fin 4 → ℚ := fun j => value (row.read j)

def run (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : Option (FixedArrayTable 4 SignedWord) × ℕ :=
  if hg : BinaryFourParentCompiler.gluingCase input=true then
    (BinaryGluingSampler.prepare input hC (gluing_guard input hC hAd hg)).runIndexed K N scalar bits 0 (Nat.zero_le N)
  else BinarySmallRootSample.run input hC (small_guard input hC hAd hg) K N outer scalar bits

theorem run_refines (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hAd : Admissible input) (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    ((run input hC hAd K N outer scalar bits).1.map sourceRow,(run input hC hAd K N outer scalar bits).2) =
      (source.machine K outer scalar).run N (source.start K outer scalar) bits := by
  unfold run
  split
  · rename_i hg
    have hs := (BinaryFourParentCompiler.gluingCase_iff input source hC hr).mp hg
    have he := (BinaryGluingSampler.prepare input hC (gluing_guard input hC hAd hg)).runIndexed_refines
      (source.gluingDescriptor hs) (BinaryGluingSampler.prepare_refines input source hC _ hr hs) K N scalar bits 0 (Nat.zero_le N)
    rw [WordStateMachine.run_eq_numeric,WordStateMachine.runNumeric,BinaryGluingSampler.source_gluing_indexed source hs K N outer scalar bits] at ⊢
    exact he
  · rename_i hg
    have hs := lt_of_not_ge (fun h => hg ((BinaryFourParentCompiler.gluingCase_iff input source hC hr).mpr h))
    have he := BinarySmallRootSample.run_refines input source hC hr hs (small_guard input hC hAd hg) K N outer scalar bits
    rw [WordStateMachine.run_eq_numeric,WordStateMachine.runNumeric]
    unfold RationalFourInput.start
    rw [dite_eq_right (not_le.mpr hs)]
    have ht := source.small_runIndexed hs K N outer scalar bits (.state BinaryState.start) 0 (Nat.zero_le N)
    simp only [WordCursor.mapState] at ht
    rw [ht,← WordStateMachine.runNumeric,← WordStateMachine.run_eq_numeric]
    exact he

theorem run_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (row : FixedArrayTable 4 SignedWord)
    (hs : (run input hC hAd K N outer scalar bits).1=some row) : ∀ j, CanonicalWord (row.read j) := by
  unfold run at hs
  split at hs
  · obtain ⟨slot,hSlot,rfl⟩ := Option.map_eq_some_iff.mp hs
    exact BinarySegmentPoint.sample_canonical _ slot K scalar (BinaryGluingSampler.prepare input hC _).canonical
  · exact BinarySmallRootSample.run_canonical input hC _ K N outer scalar bits row hs

def runIndexed (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) : Option (FixedArrayTable 4 SignedWord) × ℕ :=
  let result := run input hC hAd K (N-pos) outer scalar (WordStateMachine.inputWindow bits pos (N-pos) (by omega))
  (result.1,pos+result.2)

theorem runIndexed_refines (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hAd : Admissible input) (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool)
    (pos : ℕ) (hp : pos ≤ N) :
    ((runIndexed input hC hAd K N outer scalar bits pos hp).1.map sourceRow,(runIndexed input hC hAd K N outer scalar bits pos hp).2) =
      (source.machine K outer scalar).runCursorIndexed N bits (.state (source.start K outer scalar)) pos hp := by
  have he := run_refines input source hC hr hAd K (N-pos) outer scalar (WordStateMachine.inputWindow bits pos (N-pos) (by omega))
  rw [(source.machine K outer scalar).runCursorIndexed_window N bits (.state (source.start K outer scalar)) pos (N-pos) (by omega)]
  have hRun := WordStateMachine.run_eq_numeric (source.machine K outer scalar) (N-pos) (source.start K outer scalar)
    (WordStateMachine.inputWindow bits pos (N-pos) (by omega))
  rw [WordStateMachine.runNumeric,WordStateMachine.runCursorIndexed_zero] at hRun
  rw [← hRun]
  exact congrArg (fun result : Option (Fin 4 → ℚ) × ℕ => (result.1,pos+result.2)) he

theorem runIndexed_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N)
    (row : FixedArrayTable 4 SignedWord) (hs : (runIndexed input hC hAd K N outer scalar bits pos hp).1=some row) :
    ∀ j, CanonicalWord (row.read j) := run_canonical input hC hAd K (N-pos) outer scalar _ row hs

end Blotto.BinaryFourPartialRun
