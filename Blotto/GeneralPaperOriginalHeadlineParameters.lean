import Blotto.GeneralPaperMeasuredEqualFullContract

/-! One paper input/accuracy scale before branch selection. These erased
observers describe retained input lengths; preparation never measures them
again to select a source or reference. -/
namespace Blotto.GeneralPaperOriginalHeadlineParameters
open GeneralPaperOriginalGameInput
set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def inputSize (p : Input) : ℕ := GeneralPaperValueRoundingInputPrice.inputSize p.values +
  rationalWordWidth p.budget + GeneralPaperBinaryAccuracyConstructionStorage.inputSize p.words + 1

def logarithm (p : Input) : ℕ := 129 + binaryWordWidth (p.n + 4) +
  binaryWordWidth ⌈(epsilon p)⁻¹⌉₊ + binaryWordWidth (inputSize p + 1)

def nStar (p : Input) : ℚ := GeneralPaperRealHeadlineParameters.nStar p.n (epsilon p)
def timeScale (p : Input) : ℚ := (inputSize p : ℚ) + nStar p ^ 3 / epsilon p ^ 6
def spaceScale (p : Input) : ℚ := (inputSize p : ℚ) + nStar p ^ 3 / epsilon p ^ 4
def descriptionScale (p : Input) : ℚ := (inputSize p : ℚ) + p.n + nStar p ^ 2 / epsilon p ^ 3

theorem input_positive (p : Input) : 1 ≤ inputSize p := by unfold inputSize; omega
theorem log_positive (p : Input) : 1 ≤ logarithm p := by unfold logarithm; omega

theorem nstar_nonnegative (p : Input) : 0 ≤ nStar p := by
  have he := epsilon_positive p
  unfold nStar GeneralPaperRealHeadlineParameters.nStar
  positivity

theorem time_ge_input (p : Input) : (inputSize p : ℚ) ≤ timeScale p := by
  have he := epsilon_positive p
  have hn := nstar_nonnegative p
  have h : 0 ≤ nStar p ^ 3 / epsilon p ^ 6 := by positivity
  unfold timeScale
  linarith only [h]

theorem space_ge_input (p : Input) : (inputSize p : ℚ) ≤ spaceScale p := by
  have he := epsilon_positive p
  have hn := nstar_nonnegative p
  have h : 0 ≤ nStar p ^ 3 / epsilon p ^ 4 := by positivity
  unfold spaceScale
  linarith only [h]

theorem description_ge_input (p : Input) : (inputSize p : ℚ) ≤ descriptionScale p := by
  have he := epsilon_positive p
  have h : 0 ≤ nStar p ^ 2 / epsilon p ^ 3 := by positivity
  unfold descriptionScale
  nlinarith only [h, Nat.cast_nonneg (α := ℚ) p.n]

theorem equal_input (model : RationalCostModel) (p : Input) :
    GeneralPaperEqualInputHeadline.inputSize (equalInput model p) = inputSize p := rfl

theorem equal_log (model : RationalCostModel) (p : Input) :
    GeneralPaperEqualInputHeadline.paperLog (equalInput model p) ≤ logarithm p := by
  change 129 + binaryWordWidth ⌈(epsilon p)⁻¹⌉₊ + binaryWordWidth (inputSize p + 1) ≤ _
  unfold logarithm
  omega

theorem native_ledger (p : Input) (h : p.budget < 1) :
    GeneralPaperNativeResourceDomain.ledger (unequalInput p h) + 1 ≤ 4 * inputSize p := by
  dsimp only [GeneralPaperNativeResourceDomain.ledger, GeneralPaperNativeResourceDomain.originalInputSize,
    GeneralPaperNativeResourceDomain.originalSize, GeneralPaperNativeResourceDomain.accuracySize, unequalInput, inputSize]
  omega

theorem native_log (p : Input) (h : p.budget < 1) :
    GeneralPaperNativeWorkingSpaceHeadline.paperLog (unequalInput p h) ≤ 2 * logarithm p := by
  have hl := binaryWordWidth_mono (native_ledger p h)
  have hm := binaryWordWidth_mul 4 (inputSize p)
  rw [show binaryWordWidth 4 = 3 by decide] at hm
  have hi := binaryWordWidth_mono (show inputSize p ≤ inputSize p + 1 by omega)
  change 129 + binaryWordWidth (p.n + 4) + binaryWordWidth ⌈(epsilon p)⁻¹⌉₊ +
    binaryWordWidth (GeneralPaperNativeResourceDomain.ledger (unequalInput p h) + 1) ≤ _
  unfold logarithm
  omega

end Blotto.GeneralPaperOriginalHeadlineParameters
