import Blotto.BinarySmallRootPrimitiveRun
import Blotto.BinaryReflectedFallbackFactory

/-! Complete small-case bounded draws use the exact measured lower fallback
after root/continuation exhaustion. Every bit path returns the original row.
Canonical hard budgets, exact finite-bit law/CDF scope and source-derived
recorded primitive bounds transfer. Whole-model/physical costs remain separate. -/

namespace Blotto.BinarySmallFixedPrimitiveWork
open MeasureTheory
open BinaryRationalNormalization BinaryRationalEncoding BinarySmallRootSample

def fixedSampleWithWork (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : FixedArrayTable 4 SignedWord × ℕ :=
  let drawn := BinarySmallRootPrimitiveRun.run input hC hAd K N outer scalar bits
  match drawn.1.1 with
  | some row => (row,drawn.2.recorded)
  | none =>
      let fallback := BinaryReflectedFallbackFactory.sampleWithWork input hC hAd K outer scalar
      (fallback.1,drawn.2.recorded + fallback.2.recorded)

theorem fixedSampleWithWork_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (fixedSampleWithWork input hC hAd K N outer scalar bits).1 = fixedSample input hC hAd K N outer scalar bits := by
  unfold fixedSampleWithWork fixedSample
  dsimp only
  rw [← BinarySmallRootPrimitiveRun.run_state input hC hAd K N outer scalar bits]
  cases he : (BinarySmallRootPrimitiveRun.run input hC hAd K N outer scalar bits).1.1 with
  | none => exact BinaryReflectedFallbackFactory.sampleWithWork_state input hC hAd K outer scalar
  | some row => rfl

def fixedBound (s K N : ℕ) : ℕ := BinarySmallRootPrimitiveRun.bound s K N + BinaryReflectedFallbackFactory.bound s K

theorem fixedSampleWithWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : Admissible input)
    (hCase : source.w < (1 - source.p) * source.ell) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (fixedSampleWithWork input hC hAd K N outer scalar bits).2 ≤ fixedBound s K N := by
  have hDraw := BinarySmallRootPrimitiveRun.run_bound input source hC hR hAd hCase s hs hH K N outer scalar bits
  have hFallback := BinaryReflectedFallbackFactory.sampleWithWork_bound input source hC hR hCase hAd s hs hH K outer scalar
  unfold fixedSampleWithWork
  dsimp only
  split <;> dsimp only <;> unfold fixedBound <;> omega

theorem fixedSampleWithWork_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    ∀ j, CanonicalWord ((fixedSampleWithWork input hC hAd K N outer scalar bits).1.read j) := by
  rw [fixedSampleWithWork_state]
  exact fixedSample_canonical input hC hAd K N outer scalar bits

theorem fixedSampleWithWork_fullBudget (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : Admissible input)
    (hCase : source.w < (1 - source.p) * source.ell) (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    FullBudget (source.B : ℝ) (fun j => (value ((fixedSampleWithWork input hC hAd K N outer scalar bits).1.read j) : ℝ)) := by
  rw [fixedSampleWithWork_state]
  exact fixedSample_fullBudget input source hC hR hCase hAd K N outer scalar bits

theorem fixedSampleWithWork_inBox (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : Admissible input)
    (hCase : source.w < (1 - source.p) * source.ell) (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    InBox ![(source.u : ℝ),(source.v : ℝ),(source.w : ℝ),(source.ell : ℝ)]
      (fun j => (value ((fixedSampleWithWork input hC hAd K N outer scalar bits).1.read j) : ℝ)) := by
  rw [fixedSampleWithWork_state]
  exact fixedSample_inBox input source hC hR hCase hAd K N outer scalar bits

def sampleWithWork (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input) (K : ℕ)
    (bits : Fin (RationalFourInput.smallSampleBitBudget K) → Bool) : FixedArrayTable 4 SignedWord × ℕ :=
  let inner := firstBitBlock (RationalFourInput.smallInnerBitBudget K) K bits
  let outer := secondBitBlock (RationalFourInput.smallInnerBitBudget K) K bits
  fixedSampleWithWork input hC hAd K (RationalFourInput.smallCoinBitBudget K) outer
    (secondBitBlock (RationalFourInput.smallCoinBitBudget K) K inner)
    (firstBitBlock (RationalFourInput.smallCoinBitBudget K) K inner)

theorem sampleWithWork_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input) (K : ℕ)
    (bits : Fin (RationalFourInput.smallSampleBitBudget K) → Bool) :
    (sampleWithWork input hC hAd K bits).1 = sample input hC hAd K bits :=
  fixedSampleWithWork_state input hC hAd K _ _ _ _

def bound (s K : ℕ) : ℕ := fixedBound s K (RationalFourInput.smallCoinBitBudget K)

theorem sampleWithWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : Admissible input)
    (hCase : source.w < (1 - source.p) * source.ell) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K : ℕ) (bits : Fin (RationalFourInput.smallSampleBitBudget K) → Bool) :
    (sampleWithWork input hC hAd K bits).2 ≤ bound s K :=
  fixedSampleWithWork_bound input source hC hR hAd hCase s hs hH K _ _ _ _

theorem sampleWithWork_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input) (K : ℕ)
    (bits : Fin (RationalFourInput.smallSampleBitBudget K) → Bool) :
    ∀ j, CanonicalWord ((sampleWithWork input hC hAd K bits).1.read j) := by
  rw [sampleWithWork_state]
  exact sample_canonical input hC hAd K bits

theorem sampleWithWork_fullBudget (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : Admissible input)
    (hCase : source.w < (1 - source.p) * source.ell) (K : ℕ) (bits : Fin (RationalFourInput.smallSampleBitBudget K) → Bool) :
    FullBudget (source.B : ℝ) (fun j => (value ((sampleWithWork input hC hAd K bits).1.read j) : ℝ)) := by
  rw [sampleWithWork_state]
  exact sample_fullBudget input source hC hR hCase hAd K bits

noncomputable def sampleLaw (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input) (K : ℕ) : Mixed 4 :=
  (fairBitLaw (RationalFourInput.smallSampleBitBudget K)).map (fun bits j => (value ((sampleWithWork input hC hAd K bits).1.read j) : ℝ))

theorem sampleLaw_eq (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input) (K : ℕ) :
    sampleLaw input hC hAd K = BinarySmallRootSample.sampleLaw input hC hAd K := by
  unfold sampleLaw BinarySmallRootSample.sampleLaw
  congr 1
  funext bits j
  rw [sampleWithWork_state]

theorem sampleLaw_CDF_error (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : Admissible input)
    (hCase : source.w < (1 - source.p) * source.ell) (K : ℕ) :
    CDFClose (sampleLaw input hC hAd K) (source.real.smallCaseLaw (source.smallCase_real hCase)) (5 / (2 * (2 : ℝ) ^ K)) := by
  rw [sampleLaw_eq]
  exact BinarySmallRootSample.sampleLaw_CDF_error input source hC hR hCase hAd K

end Blotto.BinarySmallFixedPrimitiveWork
