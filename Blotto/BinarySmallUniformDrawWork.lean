import Blotto.BinaryStoredSegmentDrawWork
import Blotto.BinarySmallRootSample
import Blotto.RationalMergeFourHeight

/-! The small four-variable uniform continuation uses its actual stored
nine-slot table and the caller's shared absolute position. Weight/endpoint
heights follow the original six-word source, with no supplied cursor/word oracle.
Descriptor construction, the root coin and reflected continuation are separate
ledger joins; this module prices the actual selected indexed draw. -/

namespace Blotto.BinarySmallUniformDrawWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySmallRootSample

def prepared (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input) :
    BinaryStoredSegmentProgram.Prepared 4 9 :=
  ⟨BinarySmallUniformCompiler.fromOriginal input, BinarySmallUniformCompiler.fromOriginal_canonical input hC,
    uniform_nonnegative input hC hAd⟩

def runIndexedWithWork (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (Option (FixedArrayTable 4 SignedWord) × ℕ) × ℕ :=
  BinaryStoredSegmentDrawWork.runIndexedWork (prepared input hC hAd) 0 K N scalar bits pos hp

theorem runIndexedWithWork_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (runIndexedWithWork input hC hAd K N scalar bits pos hp).1 = uniformRun input hC hAd K N scalar bits pos hp :=
  BinaryStoredSegmentDrawWork.runIndexedWork_state (prepared input hC hAd) 0 K N scalar bits pos hp

def bound (s K remaining : ℕ) : ℕ :=
  BinaryStoredSegmentChoiceWork.selectionBound 9 (expressionHeightBudget s 35) remaining +
    BinaryStoredSegmentDrawWork.pointBound 4 (expressionHeightBudget s 35) K

theorem runIndexedWithWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hAd : Admissible input)
    (hCase : source.w < (1 - source.p) * source.ell) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (runIndexedWithWork input hC hAd K N scalar bits pos hp).2 ≤ bound s K (N - pos) := by
  have hTable := BinarySmallUniformCompiler.fromOriginal_refines input source hC hR hCase
  have hHeight := hH.smallUniformLottery hs hCase
  exact BinaryStoredSegmentDrawWork.runIndexedWork_bound (prepared input hC hAd) (source.smallUniformLottery hCase)
    hTable (expressionHeightBudget s 35) (expressionHeightBudget s 35)
    (hs.trans (expressionHeightBudget_ge_input s 35)) hHeight.1 hHeight.2 0 K N scalar bits pos hp

end Blotto.BinarySmallUniformDrawWork
