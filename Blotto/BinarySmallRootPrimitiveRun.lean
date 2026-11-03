import Blotto.BinaryStoredCoinIndexedWork
import Blotto.BinarySmallUniformFactoryDraw
import Blotto.BinaryReflectedFactoryRun
import Blotto.BinaryReflectedIndexedRun

/-! The actual small root normalizes its stored probability once, executes its
measured indexed coin, and hands its returned position to one chosen producer.
The primitive ledger joins the uniform factory/draw or the reflected resource/
terminal/factory/draw. It preserves all retained row/none/position semantics.
Reflected pre-resource setup, fallback and complete model costs remain separate. -/

namespace Blotto.BinarySmallRootPrimitiveRun
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinarySmallRootSample

def rootWithWork (input : BinaryFourParameters.Input) (N : ℕ) (bits : Fin N → Bool) : (Option Bool × ℕ) × ℕ :=
  let probability := canonicalizeWithWork input.p
  let root := BinaryStoredCoinIndexedWork.sampleWithWork probability.1 N bits 0 (Nat.zero_le N)
  (root.1,probability.2 + root.2)

theorem rootWithWork_state (input : BinaryFourParameters.Input) (N : ℕ) (bits : Fin N → Bool) :
    (rootWithWork input N bits).1 = BinaryStoredCoinIndexed.sample (probability input) N bits 0 (Nat.zero_le N) := by
  unfold rootWithWork probability
  rw [BinaryStoredCoinIndexedWork.sampleWithWork_state,canonicalizeWithWork_state]

def rootBound (s N : ℕ) : ℕ := 170 * (2 + 2 * s) ^ 3 + BinaryStoredCoinIndexedWork.bound (1 + 2 * s) N

theorem rootWithWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (s : ℕ) (hH : source.FieldsHeight s)
    (N : ℕ) (bits : Fin N → Bool) : (rootWithWork input N bits).2 ≤ rootBound s N := by
  have hp : RationalHeight (value input.p) s := by rw [hR.2.2.2.2.2]; exact hH.2.2.2.2.2
  have hw := hC.2.2.2.2.2.2.trans (rationalWordWidth_of_height hp)
  have hNormalize := (canonicalizeWithWork_bound input.p).trans
    (Nat.mul_le_mul_left 170 (Nat.pow_le_pow_left (Nat.add_le_add_right hw 1) 3))
  have hProbability := (BinaryPRGPreparationWork.canonicalize_stored_width input.p).trans hw
  have hRoot := BinaryStoredCoinIndexedWork.sampleWithWork_bound (probability input) N bits 0 (Nat.zero_le N) _ hProbability
  unfold rootWithWork
  dsimp only
  rw [canonicalizeWithWork_state]
  simpa only [rootBound,probability,Nat.sub_zero,show 1 + 2 * s + 1 = 2 + 2 * s by omega] using Nat.add_le_add hNormalize hRoot

def reflectedIndexedWithWork (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (Option (FixedArrayTable 4 SignedWord) × ℕ) × ℕ :=
  let result := BinaryReflectedFactoryRun.run input hC hAd K (N - pos) outer scalar
    (WordStateMachine.inputWindow bits pos (N - pos) (by omega))
  ((result.1.1,pos + result.1.2),result.2.recorded)

theorem reflectedIndexedWithWork_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (reflectedIndexedWithWork input hC hAd K N outer scalar bits pos hp).1 =
      BinaryReflectedIndexedRun.run input hC hAd K N outer scalar bits pos hp := by
  unfold reflectedIndexedWithWork BinaryReflectedIndexedRun.run
  simp only [BinaryReflectedFactoryRun.run_state]

structure Ledger where
  root : ℕ
  uniform : ℕ
  reflected : ℕ
  deriving Repr, DecidableEq

def Ledger.recorded (ledger : Ledger) : ℕ := ledger.root + ledger.uniform + ledger.reflected

def run (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (Option (FixedArrayTable 4 SignedWord) × ℕ) × Ledger :=
  let root := rootWithWork input N bits
  match root.1.1 with
  | none => ((none,root.1.2),⟨root.2,0,0⟩)
  | some branch =>
      if hp : root.1.2 ≤ N then
        if branch then
          let drawn := BinarySmallUniformFactoryDraw.runIndexedWithWork input hC hAd K N scalar bits root.1.2 hp
          (drawn.1,⟨root.2,drawn.2,0⟩)
        else
          let drawn := reflectedIndexedWithWork input hC hAd K N outer scalar bits root.1.2 hp
          (drawn.1,⟨root.2,0,drawn.2⟩)
      else ((none,root.1.2),⟨root.2,0,0⟩)

theorem run_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (run input hC hAd K N outer scalar bits).1 = BinarySmallRootSample.run input hC hAd K N outer scalar bits := by
  unfold run BinarySmallRootSample.run
  dsimp only
  rw [← rootWithWork_state input N bits]
  cases he : (rootWithWork input N bits).1.1 with
  | none => rfl
  | some branch =>
      dsimp only
      split
      · split
        · exact BinarySmallUniformFactoryDraw.runIndexedWithWork_state input hC hAd K N scalar bits _ _
        · exact reflectedIndexedWithWork_state input hC hAd K N outer scalar bits _ _
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

def bound (s K N : ℕ) : ℕ := rootBound s N + BinarySmallUniformFactoryDraw.bound s K N + BinaryReflectedFactoryRun.bound s K N

theorem run_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : Admissible input)
    (hCase : source.w < (1 - source.p) * source.ell) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (run input hC hAd K N outer scalar bits).2.recorded ≤ bound s K N := by
  have hRoot := rootWithWork_bound input source hC hR s hH N bits
  unfold run
  dsimp only
  split
  · dsimp only [Ledger.recorded]; unfold bound; omega
  · split
    · rename_i hp
      split
      · have hUniform := BinarySmallUniformFactoryDraw.runIndexedWithWork_bound input source hC hR hAd hCase s hs hH
          K N scalar bits (rootWithWork input N bits).1.2 hp
        have hUN := hUniform.trans (uniform_bound_mono s K (Nat.sub_le _ _))
        dsimp only [Ledger.recorded]
        unfold bound
        omega
      · have hReflected := BinaryReflectedFactoryRun.run_bound input source hC hR hCase hAd s hs hH K
          (N - (rootWithWork input N bits).1.2) outer scalar
          (WordStateMachine.inputWindow bits (rootWithWork input N bits).1.2 (N - (rootWithWork input N bits).1.2) (by omega))
        have hRN := hReflected.trans (reflected_bound_mono s K (Nat.sub_le _ _))
        dsimp only [Ledger.recorded,reflectedIndexedWithWork]
        unfold bound
        omega
    · dsimp only [Ledger.recorded]; unfold bound; omega

theorem run_canonical (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (row : FixedArrayTable 4 SignedWord)
    (h : (run input hC hAd K N outer scalar bits).1.1 = some row) : ∀ j, CanonicalWord (row.read j) := by
  rw [run_state] at h
  exact BinarySmallRootSample.run_canonical input hC hAd K N outer scalar bits row h

end Blotto.BinarySmallRootPrimitiveRun
