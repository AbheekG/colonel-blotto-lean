import Blotto.BinaryReflectedOutput

/-! The native serial entry point retains the resource run's complete result
once, then passes its position to the categorical reader. This exact wrapper
avoids repeated resource execution while preserving all earlier statements. -/

namespace Blotto.BinaryReflectedCachedRun
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedFourSetup
open BinarySharedResourceRun BinaryReflectedSerialRun

def select (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer : Fin K → Bool) (bits : Fin N → Bool) :
    Option (BinaryThreeResourcePair.Certified (prepare input).capacity × Fin 18) × ℕ :=
  let reached := setupRun input hC N bits
  match hResult : reached.1 with
  | none => (none,reached.2)
  | some result =>
      let table := BinaryTerminalProfileCompiler.profile (prepare input) result.state K outer
      let chosen := BinaryCategoricalRun.runIndexed (0 : Fin 18) N bits
        (.remaining (NativeBinarySegmentSampler.weights table
          (BinaryTerminalProfileCompiler.profile_canonical _ result.state (prepare_canonical input hC) result.canonical K outer)
          (profile_nonnegative input hC hAd N bits result hResult K outer)))
        reached.2 (setupRun_position input hC N bits)
      (chosen.1.map (fun slot => (result,slot)),chosen.2)

theorem select_eq (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer : Fin K → Bool) (bits : Fin N → Bool) :
    select input hC hAd K N outer bits = BinaryReflectedSerialRun.select input hC hAd K N outer bits := rfl

def run (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : Option (FixedArrayTable 4 SignedWord) × ℕ :=
  let selected := select input hC hAd K N outer bits
  (selected.1.map (fun pair => BinaryReflectedTerminalEmission.sample input pair.1.state K outer scalar pair.2),selected.2)

theorem run_eq (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    run input hC hAd K N outer scalar bits = BinaryReflectedSerialRun.run input hC hAd K N outer scalar bits := rfl

def fixedSample (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : FixedArrayTable 4 SignedWord :=
  match (run input hC hAd K N outer scalar bits).1 with
  | some row => row
  | none => BinaryTerminalFallback.sample input hC hAd K outer scalar

theorem fixedSample_eq (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    fixedSample input hC hAd K N outer scalar bits = BinaryReflectedOutput.fixedSample input hC hAd K N outer scalar bits := rfl

end Blotto.BinaryReflectedCachedRun
