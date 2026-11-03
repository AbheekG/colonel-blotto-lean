import Blotto.GeneralPaperOriginalGameInput

/-! The measured original-input logarithm and the unequal source-analysis
logarithm are comparable. No source construction is used to measure input. -/
namespace Blotto.GeneralPaperOriginalReferenceComparison
open GeneralPaperOriginalGameInput
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def logarithm (model : RationalCostModel) (p : Input) : ℕ :=
  GeneralPaperEqualInputDomain.logarithm (equalInput model p)

theorem ledger_bounds (model : RationalCostModel) (p : Input) (h : p.budget < 1) :
    GeneralPaperNativeResourceDomain.ledger (unequalInput p h) + 1 ≤
      4 * GeneralPaperEqualInputDomain.ledger (equalInput model p) ∧
    p.n + 4 ≤ 4 * GeneralPaperEqualInputDomain.ledger (equalInput model p) ∧
    GeneralPaperEqualInputDomain.ledger (equalInput model p) ≤
      2 * (GeneralPaperNativeResourceDomain.ledger (unequalInput p h) + 1) := by
  have hn := GeneralPaperOriginalValueBitDriverRate.input_fields p.values
  dsimp only [GeneralPaperEqualInputDomain.ledger, GeneralPaperEqualInputDomain.originalSize,
    GeneralPaperEqualInputDomain.budgetSize, GeneralPaperEqualInputDomain.accuracySize,
    GeneralPaperNativeResourceDomain.ledger, GeneralPaperNativeResourceDomain.originalInputSize,
    GeneralPaperNativeResourceDomain.originalSize, GeneralPaperNativeResourceDomain.accuracySize,
    equalInput, unequalInput]
  omega

theorem native_log_le (model : RationalCostModel) (p : Input) (h : p.budget < 1) :
    GeneralPaperNativeResourceDomain.logarithm model (unequalInput p h) ≤ 8 * logarithm model p := by
  let q := unequalInput p h
  let B := GeneralPaperEqualInputDomain.ledger (equalInput model p)
  have hB := ledger_bounds model p h
  have hn := binaryWordWidth_mono hB.2.1
  have he := binaryWordWidth_mono hB.1
  have hm := binaryWordWidth_mul 4 B
  rw [show binaryWordWidth 4 = 3 by decide] at hm
  have hLog := (GeneralPaperOriginalSourceValueContract.original_log_bound false model 1
    (GeneralPaperNativeResourceDomain.exponent q) (GeneralPaperNativeResourceDomain.ledger q)
    p.values p.selector p.correct p.budget q.budget_valid
    ((GeneralPaperNativeResourceDomain.budget_height q).mono
      (by unfold GeneralPaperNativeResourceDomain.ledger GeneralPaperNativeResourceDomain.originalInputSize; omega))).1
  change GeneralPaperNativeResourceDomain.logarithm model q ≤ _ at hLog
  dsimp only [GeneralPaperOriginalSourceValueContract.inputLog] at hLog
  change _ ≤ 8 * (128 + GeneralPaperNativeResourceDomain.exponent q + binaryWordWidth B)
  dsimp only [q, B] at *
  omega

theorem measured_log_le (model : RationalCostModel) (p : Input) (h : p.budget < 1) :
    logarithm model p ≤ 2 * GeneralPaperNativeResourceDomain.logarithm model (unequalInput p h) := by
  let q := unequalInput p h
  have he := binaryWordWidth_mono (ledger_bounds model p h).2.2
  have hm := binaryWordWidth_mul 2 (GeneralPaperNativeResourceDomain.ledger q + 1)
  rw [show binaryWordWidth 2 = 2 by decide] at hm
  have hl : 128 + GeneralPaperNativeResourceDomain.exponent q +
      binaryWordWidth (GeneralPaperNativeResourceDomain.ledger q + 1) ≤
      GeneralPaperNativeResourceDomain.logarithm model q := by
    change 128 + (GeneralPaperNativeResourceDomain.source model q).k +
      binaryWordWidth ((GeneralPaperNativeResourceDomain.source model q).B + 1) ≤
      GeneralPaperSourceWordGrowth.logSize (GeneralPaperNativeResourceDomain.source model q)
    unfold GeneralPaperSourceWordGrowth.logSize
    omega
  change 128 + GeneralPaperNativeResourceDomain.exponent q +
    binaryWordWidth (GeneralPaperEqualInputDomain.ledger (equalInput model p)) ≤ _
  dsimp only [q] at *
  omega

end Blotto.GeneralPaperOriginalReferenceComparison
