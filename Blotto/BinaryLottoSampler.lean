import Blotto.BinaryLottoSamplerRun
import Blotto.RationalLottoPaperProgram

/-! Stored Boolean general-field Lotto sampling has the exact original whole
law and global B-zero fallback. One seed uses the retained choice/scalar/outer
layout. Numerical input recognition and complete computation-model costs are
not supplied by this refinement and remain separate obligations. -/

namespace Blotto.BinaryLottoSampler
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode BinaryLottoResourceInput RationalLottoResourceSystem
open MeasureTheory

def fallback {n : ℕ} (input : Input n) : FixedArrayTable n SignedWord :=
  FixedArrayTable.ofFn (fun j => if j.val = 0 then input.budget else zero)

theorem fallback_canonical {n : ℕ} (input : Input n) (hC : input.Canonical) :
    ∀ j,CanonicalWord ((fallback input).read j) := by
  intro j
  simp only [fallback,FixedArrayTable.read_ofFn]
  split
  · exact hC.1
  · exact zero_canonical

theorem fallback_refines {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hr : input.Refines source) : BinaryTerminalPartialRun.sourceRow (fallback input) = source.fallbackAllocation := by
  funext j
  change value ((fallback input).read j) = source.fallbackAllocation j
  simp only [fallback,FixedArrayTable.read_ofFn,RationalLottoResourceSystem.fallbackAllocation]
  have hj : j = source.firstField ↔ j.val = 0 := by
    constructor
    · intro he; rw [he]; rfl
    · intro he; exact Fin.ext he
  by_cases hz : j.val = 0
  · simp only [ite_eq_left hz,ite_eq_left (hj.mpr hz)]
    exact hr.1
  · simp only [hz,ite_false,show j ≠ source.firstField from fun he => hz (hj.mp he),zero_value]

def fixedSample {n : ℕ} (input : Input n) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : FixedArrayTable n SignedWord :=
  (BinaryLottoSamplerRun.run input hC hAd K N outer scalar bits).1.getD (fallback input)

theorem fixedSample_refines {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hC : input.Canonical) (hr : input.Refines source) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    BinaryTerminalPartialRun.sourceRow (fixedSample input hC hAd K N outer scalar bits) =
      source.paperFixedSample K N outer scalar bits := by
  have he := congrArg Prod.fst (BinaryLottoSamplerRun.run_refines input source hC hr hAd K N outer scalar bits)
  rw [source.paperFixedSample_refines]
  unfold RationalLottoResourceSystem.paperFixedSampleReference WordStateMachine.output fixedSample
  rw [←he]
  cases hs : (BinaryLottoSamplerRun.run input hC hAd K N outer scalar bits).1 with
  | none => simpa only [Option.map_none,Option.getD_none] using fallback_refines input source hr
  | some row => rfl

theorem fixedSample_canonical {n : ℕ} (input : Input n) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    ∀ j,CanonicalWord ((fixedSample input hC hAd K N outer scalar bits).read j) := by
  unfold fixedSample
  cases hs : (BinaryLottoSamplerRun.run input hC hAd K N outer scalar bits).1 with
  | none => exact fallback_canonical input hC
  | some row => exact BinaryLottoSamplerRun.run_canonical input hC hAd K N outer scalar bits row hs

theorem fixedSample_fullBudget {n : ℕ} (input : Input n) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    FullBudget (value input.budget : ℝ) (fun j => (value ((fixedSample input hC hAd K N outer scalar bits).read j) : ℝ)) := by
  obtain ⟨source,hr⟩ := hAd
  have he := fixedSample_refines input source hC hr (show Admissible input from ⟨source,hr⟩) K N outer scalar bits
  have heR := congrArg (fun row : Fin n → ℚ => fun j => (row j : ℝ)) he
  rw [hr.1]
  exact heR.symm ▸ source.paperFixedSample_fullBudget K N outer scalar bits

def innerSample {n : ℕ} (input : Input n) (hC : input.Canonical) (hAd : Admissible input) (K : ℕ)
    (outer : Fin K → Bool) (bits : Fin (innerBitBudget n K) → Bool) : FixedArrayTable n SignedWord :=
  fixedSample input hC hAd K (coinBitBudget n K) outer (secondBitBlock (coinBitBudget n K) K bits)
    (firstBitBlock (coinBitBudget n K) K bits)

def sample {n : ℕ} (input : Input n) (hC : input.Canonical) (hAd : Admissible input) (K : ℕ)
    (bits : Fin (sampleBitBudget n K) → Bool) : FixedArrayTable n SignedWord :=
  innerSample input hC hAd K (secondBitBlock (innerBitBudget n K) K bits) (firstBitBlock (innerBitBudget n K) K bits)

theorem sample_refines {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hC : input.Canonical) (hr : input.Refines source) (hAd : Admissible input)
    (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) :
    BinaryTerminalPartialRun.sourceRow (sample input hC hAd K bits) = source.paperSample K bits :=
  fixedSample_refines input source hC hr hAd K _ _ _ _

theorem sample_canonical {n : ℕ} (input : Input n) (hC : input.Canonical) (hAd : Admissible input)
    (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) :
    ∀ j,CanonicalWord ((sample input hC hAd K bits).read j) := fixedSample_canonical input hC hAd K _ _ _ _

theorem sample_fullBudget {n : ℕ} (input : Input n) (hC : input.Canonical) (hAd : Admissible input)
    (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) :
    FullBudget (value input.budget : ℝ) (fun j => (value ((sample input hC hAd K bits).read j) : ℝ)) :=
  fixedSample_fullBudget input hC hAd K _ _ _ _

noncomputable def sampleLaw {n : ℕ} (input : Input n) (hC : input.Canonical) (hAd : Admissible input) (K : ℕ) : Mixed n :=
  (fairBitLaw (sampleBitBudget n K)).map (fun bits j => (value ((sample input hC hAd K bits).read j) : ℝ))

theorem sampleLaw_refines {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hC : input.Canonical) (hr : input.Refines source) (hAd : Admissible input) (K : ℕ) :
    sampleLaw input hC hAd K = source.paperSampleLaw K := by
  have he : (fun bits j => (value ((sample input hC hAd K bits).read j) : ℝ)) =
      fun bits j => (source.paperSample K bits j : ℝ) := by
    funext bits j
    exact congrArg (fun row : Fin n → ℚ => (row j : ℝ)) (sample_refines input source hC hr hAd K bits)
  unfold sampleLaw RationalLottoResourceSystem.paperSampleLaw
  rw [he]

theorem sampleLaw_CDF_error {n : ℕ} (input : Input n) (source : RationalLottoResourceSystem n)
    (hC : input.Canonical) (hr : input.Refines source) (hAd : Admissible input) (K : ℕ) :
    CDFClose (sampleLaw input hC hAd K) source.real.law (5 / (2 * (2 : ℝ) ^ K)) := by
  rw [sampleLaw_refines input source hC hr hAd K]
  exact source.paperSampleLaw_CDF_error K

end Blotto.BinaryLottoSampler
