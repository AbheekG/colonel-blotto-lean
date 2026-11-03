import Blotto.BinaryReachedTerminal
import Blotto.NativeBinarySegmentSampler

/-! Actual Boolean reflected execution shares one reader/cap between resource
rounding and terminal categorical selection. The returned terminal position is
used without reset. Source witnesses occur only inside erased admissibility
and nonnegative-weight proofs. Failure remains explicit until fallback joins. -/

namespace Blotto.BinaryReflectedSerialRun
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedFourSetup
open BinaryThreeResourcePair BinarySharedResourceRun BinaryReachedTerminal

def Admissible (input : BinaryFourParameters.Input) : Prop :=
  ∃ source : RationalFourInput, input.Refines source ∧ source.w < (1-source.p)*source.ell

theorem setupRun_position (input : BinaryFourParameters.Input) (hC : input.Canonical) (N : ℕ) (bits : Fin N → Bool) :
    (setupRun input hC N bits).2 ≤ N := by
  rw [setupRun,run_position]
  exact WordStateMachine.run_bits_le _ _ _ _

theorem profile_nonnegative (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (N : ℕ) (bits : Fin N → Bool) (result : Certified (prepare input).capacity)
    (hSuccess : (setupRun input hC N bits).1 = some result) (K : ℕ) (outer : Fin K → Bool) :
    ∀ slot, 0 ≤ value ((BinaryTerminalProfileCompiler.profile (prepare input) result.state K outer).weight.read slot) := by
  obtain ⟨source,hr,hCase⟩ := hAd
  intro slot
  rw [(BinaryReachedTerminal.profile_refines input source hC hr hCase N bits result hSuccess K outer).1 slot]
  exact ((BinaryReachedTerminal.terminal input source hC hr hCase N bits result hSuccess).profile K outer).nonnegative slot

def select (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer : Fin K → Bool) (bits : Fin N → Bool) :
    Option (Certified (prepare input).capacity × Fin 18) × ℕ :=
  match hResult : (setupRun input hC N bits).1 with
  | none => (none,(setupRun input hC N bits).2)
  | some result =>
      let table := BinaryTerminalProfileCompiler.profile (prepare input) result.state K outer
      let chosen := BinaryCategoricalRun.runIndexed (0 : Fin 18) N bits
        (.remaining (NativeBinarySegmentSampler.weights table
          (BinaryTerminalProfileCompiler.profile_canonical _ result.state (prepare_canonical input hC) result.canonical K outer)
          (profile_nonnegative input hC hAd N bits result hResult K outer)))
        (setupRun input hC N bits).2 (setupRun_position input hC N bits)
      (chosen.1.map (fun slot => (result,slot)),chosen.2)

def run (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : Option (FixedArrayTable 4 SignedWord) × ℕ :=
  let selected := select input hC hAd K N outer bits
  (selected.1.map (fun pair => BinaryReflectedTerminalEmission.sample input pair.1.state K outer scalar pair.2),selected.2)

theorem select_position (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer : Fin K → Bool) (bits : Fin N → Bool) :
    (setupRun input hC N bits).2 ≤ (select input hC hAd K N outer bits).2 ∧
      (select input hC hAd K N outer bits).2 ≤ N := by
  unfold select
  split
  · exact ⟨le_rfl,setupRun_position input hC N bits⟩
  · exact BinaryCategoricalRun.runIndexed_position _ _ _ _ _ _

theorem select_success (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer : Fin K → Bool) (bits : Fin N → Bool) (result : Certified (prepare input).capacity) (slot : Fin 18)
    (hs : (select input hC hAd K N outer bits).1 = some (result,slot)) :
    (setupRun input hC N bits).1 = some result := by
  unfold select at hs
  split at hs
  · cases hs
  · rename_i current hCurrent
    dsimp only at hs
    obtain ⟨selected,hSelected,he⟩ := Option.map_eq_some_iff.mp hs
    have hEqual : current=result := (Prod.mk.inj he).1
    simpa only [hEqual] using hCurrent

theorem run_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (row : FixedArrayTable 4 SignedWord)
    (hs : (run input hC hAd K N outer scalar bits).1 = some row) : ∀ j, CanonicalWord (row.read j) := by
  obtain ⟨pair,hPair,rfl⟩ := Option.map_eq_some_iff.mp hs
  exact BinaryReflectedTerminalEmission.sample_canonical input pair.1.state hC pair.1.canonical K outer scalar pair.2

theorem run_fullBudget (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (row : FixedArrayTable 4 SignedWord)
    (hs : (run input hC hAd K N outer scalar bits).1 = some row) :
    FullBudget (source.B : ℝ) (fun j => (value (row.read j) : ℝ)) := by
  obtain ⟨pair,hPair,rfl⟩ := Option.map_eq_some_iff.mp hs
  exact BinaryReachedTerminal.emission_fullBudget input source hC hr hCase N bits pair.1
    (select_success input hC hAd K N outer bits pair.1 pair.2 hPair) K outer scalar pair.2

theorem run_inBox (input : BinaryFourParameters.Input) (source : RationalFourInput) (hC : input.Canonical)
    (hr : input.Refines source) (hCase : source.w < (1-source.p)*source.ell) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (row : FixedArrayTable 4 SignedWord)
    (hs : (run input hC hAd K N outer scalar bits).1 = some row) :
    InBox ![(source.u : ℝ),(source.v : ℝ),(source.w : ℝ),(source.ell : ℝ)] (fun j => (value (row.read j) : ℝ)) := by
  obtain ⟨pair,hPair,rfl⟩ := Option.map_eq_some_iff.mp hs
  exact BinaryReachedTerminal.emission_inBox input source hC hr hCase N bits pair.1
    (select_success input hC hAd K N outer bits pair.1 pair.2 hPair) K outer scalar pair.2

end Blotto.BinaryReflectedSerialRun
