import Blotto.BinaryReflectedRetainedFallback
import Blotto.BinarySmallUniformRetainedFactory
import Blotto.BinarySmallFixedPrimitiveWork

/-! One actual setup/parameter/capacity prefix is shared by the small root,
selected continuation and deterministic fallback. Original whole row/law/budget
semantics remain exact. Cold fixed/scheduled output records the prefix once;
metadata/fast-backend/real-RAM/physical-space costs remain separate. -/

namespace Blotto.BinarySmallRetainedPrimitiveWork
open MeasureTheory
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode BinarySmallRootSample
abbrev rootWithWork := BinarySmallRootPrimitiveRun.rootWithWork
abbrev rootBound := BinarySmallRootPrimitiveRun.rootBound
abbrev rootWithWork_state := BinarySmallRootPrimitiveRun.rootWithWork_state
abbrev rootWithWork_bound := BinarySmallRootPrimitiveRun.rootWithWork_bound
def reflectedIndexedWithWork (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input) (cached : BinaryReflectedSetupCache.Prepared input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (Option (FixedArrayTable 4 SignedWord) × ℕ) × ℕ :=
  let result := BinaryReflectedRetainedFactoryRun.runWithWork input hC hAd cached K (N - pos) outer scalar
    (WordStateMachine.inputWindow bits pos (N - pos) (by omega))
  ((result.1.1,pos + result.1.2),result.2.recorded)

theorem reflectedIndexedWithWork_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input) (cached : BinaryReflectedSetupCache.Prepared input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (reflectedIndexedWithWork input hC hAd cached K N outer scalar bits pos hp).1 =
      BinaryReflectedIndexedRun.run input hC hAd K N outer scalar bits pos hp := by
  unfold reflectedIndexedWithWork BinaryReflectedIndexedRun.run
  simp only [BinaryReflectedRetainedFactoryRun.runWithWork_state]

structure Ledger where
  root : ℕ
  uniform : ℕ
  reflected : ℕ
  deriving Repr, DecidableEq

def Ledger.recorded (ledger : Ledger) : ℕ := ledger.root + ledger.uniform + ledger.reflected

def runWithWork (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input) (cached : BinaryReflectedSetupCache.Prepared input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (Option (FixedArrayTable 4 SignedWord) × ℕ) × Ledger :=
  let root := rootWithWork input N bits
  match root.1.1 with
  | none => ((none,root.1.2),⟨root.2,0,0⟩)
  | some branch =>
      if hp : root.1.2 ≤ N then
        if branch then
          let drawn := BinarySmallUniformRetainedFactory.runIndexedWithWork input hC hAd cached K N scalar bits root.1.2 hp
          (drawn.1,⟨root.2,drawn.2,0⟩)
        else
          let drawn := reflectedIndexedWithWork input hC hAd cached K N outer scalar bits root.1.2 hp
          (drawn.1,⟨root.2,0,drawn.2⟩)
      else ((none,root.1.2),⟨root.2,0,0⟩)

theorem runWithWork_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input) (cached : BinaryReflectedSetupCache.Prepared input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (runWithWork input hC hAd cached K N outer scalar bits).1 = BinarySmallRootSample.run input hC hAd K N outer scalar bits := by
  unfold runWithWork BinarySmallRootSample.run
  dsimp only
  rw [← rootWithWork_state input N bits]
  cases he : (rootWithWork input N bits).1.1 with
  | none => rfl
  | some branch =>
      dsimp only
      split
      · split
        · exact BinarySmallUniformRetainedFactory.runIndexedWithWork_state input hC hAd cached K N scalar bits _ _
        · exact reflectedIndexedWithWork_state input hC hAd cached K N outer scalar bits _ _
      · rfl

theorem uniform_bound_mono (s K : ℕ) {a b : ℕ} (h : a ≤ b) :
    BinarySmallUniformFactoryDraw.bound s K a ≤ BinarySmallUniformFactoryDraw.bound s K b := by
  unfold BinarySmallUniformFactoryDraw.bound BinarySmallUniformDrawWork.bound BinaryStoredSegmentChoiceWork.selectionBound
  dsimp only
  gcongr

theorem reflected_bound_mono (s K : ℕ) {a b : ℕ} (h : a ≤ b) :
    BinaryReflectedFactoryRun.bound s K a ≤ BinaryReflectedFactoryRun.bound s K b := by
  unfold BinaryReflectedFactoryRun.bound BinaryReflectedMeasuredRun.bound BinaryReflectedResourceWork.bound
    BinaryReflectedPreparedDraw.bound BinaryReflectedCategoricalWork.bound BinaryStoredSegmentChoiceWork.selectionBound
  dsimp only
  gcongr

def runBound (s K N : ℕ) : ℕ := rootBound s N + BinarySmallUniformFactoryDraw.bound s K N + BinaryReflectedFactoryRun.bound s K N

theorem runWithWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : Admissible input) (cached : BinaryReflectedSetupCache.Prepared input)
    (hCase : source.w < (1 - source.p) * source.ell) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (runWithWork input hC hAd cached K N outer scalar bits).2.recorded ≤ runBound s K N := by
  have hRoot := rootWithWork_bound input source hC hR s hH N bits
  unfold runWithWork
  dsimp only
  split
  · dsimp only [Ledger.recorded]; unfold runBound; dsimp only [rootWithWork,rootBound] at *; omega
  · split
    · rename_i hp
      split
      · have hUniform := BinarySmallUniformRetainedFactory.runIndexedWithWork_bound input source hC hR hAd hCase cached s hs hH
          K N scalar bits (rootWithWork input N bits).1.2 hp
        have hUN := hUniform.trans (uniform_bound_mono s K (Nat.sub_le _ _))
        dsimp only [Ledger.recorded]
        unfold runBound
        dsimp only [rootWithWork,rootBound] at *
        omega
      · have hReflected := BinaryReflectedRetainedFactoryRun.runWithWork_bound input source hC hR hCase hAd cached s hs hH K
          (N - (rootWithWork input N bits).1.2) outer scalar
          (WordStateMachine.inputWindow bits (rootWithWork input N bits).1.2 (N - (rootWithWork input N bits).1.2) (by omega))
        have hRN := hReflected.trans (reflected_bound_mono s K (Nat.sub_le _ _))
        dsimp only [Ledger.recorded,reflectedIndexedWithWork]
        unfold runBound
        dsimp only [rootWithWork,rootBound] at *
        omega
    · dsimp only [Ledger.recorded]; unfold runBound; dsimp only [rootWithWork,rootBound] at *; omega

def fixedWithCache (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (cached : BinaryReflectedSetupCache.Prepared input) (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    FixedArrayTable 4 SignedWord × ℕ :=
  let drawn := runWithWork input hC hAd cached K N outer scalar bits
  match drawn.1.1 with
  | some row => (row,drawn.2.recorded)
  | none =>
      let fallback := BinaryReflectedRetainedFallback.sampleWithWork input hC hAd cached K outer scalar
      (fallback.1,drawn.2.recorded + fallback.2.recorded)

theorem fixedWithCache_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (cached : BinaryReflectedSetupCache.Prepared input) (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (fixedWithCache input hC hAd cached K N outer scalar bits).1 = fixedSample input hC hAd K N outer scalar bits := by
  unfold fixedWithCache fixedSample
  dsimp only
  rw [← runWithWork_state input hC hAd cached K N outer scalar bits]
  cases he : (runWithWork input hC hAd cached K N outer scalar bits).1.1 with
  | none => exact BinaryReflectedRetainedFallback.sampleWithWork_state input hC hAd cached K outer scalar
  | some row => rfl

def warmBound (s K N : ℕ) : ℕ := runBound s K N + BinaryReflectedFallbackFactory.bound s K

theorem fixedWithCache_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : Admissible input) (cached : BinaryReflectedSetupCache.Prepared input)
    (hCase : source.w < (1 - source.p) * source.ell) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (fixedWithCache input hC hAd cached K N outer scalar bits).2 ≤ warmBound s K N := by
  have hDraw := runWithWork_bound input source hC hR hAd cached hCase s hs hH K N outer scalar bits
  have hFallback := BinaryReflectedRetainedFallback.sampleWithWork_bound input source hC hR hCase hAd cached s hs hH K outer scalar
  unfold fixedWithCache
  dsimp only
  split <;> dsimp only <;> unfold warmBound <;> omega

def fixedSampleWithWork (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : FixedArrayTable 4 SignedWord × ℕ :=
  let cached := BinaryReflectedSetupCache.prepareCache input hC
  let drawn := fixedWithCache input hC hAd cached K N outer scalar bits
  (drawn.1,cached.prefixWork + drawn.2)

theorem fixedSampleWithWork_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (fixedSampleWithWork input hC hAd K N outer scalar bits).1 = fixedSample input hC hAd K N outer scalar bits :=
  fixedWithCache_state input hC hAd _ K N outer scalar bits

def fixedBound (s K N : ℕ) : ℕ := BinaryReflectedSetupCache.bound s + warmBound s K N

theorem fixedSampleWithWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : Admissible input)
    (hCase : source.w < (1 - source.p) * source.ell) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (fixedSampleWithWork input hC hAd K N outer scalar bits).2 ≤ fixedBound s K N :=
  Nat.add_le_add (BinaryReflectedSetupCache.prepareCache_bound input source hC hR hCase s hs hH)
    (fixedWithCache_bound input source hC hR hAd _ hCase s hs hH K N outer scalar bits)

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

end Blotto.BinarySmallRetainedPrimitiveWork
