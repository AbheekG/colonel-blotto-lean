import Blotto.GeneralPaperMeasuredUnequalSampling

/-! The actual once-only initializer has an additive original-input rate
on the unequal domain. Repricing compares one execution without repeating
accuracy selection or input-length measurement. -/
namespace Blotto.GeneralPaperMeasuredUnequalInitializationRates
open GeneralPaperNativeResourceDomain GeneralPaperUniformResourceGrowth
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def work (model : RationalCostModel) (K : ℕ) (p : Problem) : ℕ :=
  (GeneralPaperOriginalMeasuredReference.prepare model 1 K (GeneralPaperMeasuredReferenceGrowth.original p)).2

theorem rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (K : ℕ) (hK : 1 ≤ K) : Bound (work model K) (fun p => ledger p + 1) (logarithm model) := by
  obtain ⟨A, e, hA⟩ := GeneralPaperEqualInputRates.initialization_price_rate model hFast K
  refine ⟨2 * A * 2 ^ e, e, fun p => ?_⟩
  let input := GeneralPaperMeasuredReferenceGrowth.original p
  let ep := GeneralPaperOriginalGameInput.equalInput model input
  have hW : 1 ≤ GeneralPaperEqualInputDomain.word K ep :=
    Nat.mul_le_mul hK (GeneralPaperEqualInputDomain.logarithm_positive ep)
  have hi := GeneralPaperMeasuredInitializerMonotonicity.initialization model 1 _ K hW ep
  have hInit : work model K p ≤ GeneralPaperEqualInputInitialization.initializationPrice model
      (GeneralPaperEqualInputDomain.word K ep) K ep :=
    hi.trans (GeneralPaperEqualInputInitialization.initialization_work model _ K ep)
  have hLog : GeneralPaperEqualInputDomain.logarithm ep ≤ 2 * logarithm model p :=
    GeneralPaperOriginalReferenceComparison.measured_log_le model input p.budget_valid.2
  have hLedger : GeneralPaperEqualInputDomain.ledger ep ≤ 2 * (ledger p + 1) :=
    (GeneralPaperOriginalReferenceComparison.ledger_bounds model input p.budget_valid.2).2.2
  calc
    _ ≤ GeneralPaperEqualInputInitialization.initializationPrice model
        (GeneralPaperEqualInputDomain.word K ep) K ep := hInit
    _ ≤ A * GeneralPaperEqualInputDomain.ledger ep * (GeneralPaperEqualInputDomain.logarithm ep) ^ e := hA ep
    _ ≤ A * (2 * (ledger p + 1)) * (2 * logarithm model p) ^ e :=
      Nat.mul_le_mul (Nat.mul_le_mul_left A hLedger) (Nat.pow_le_pow_left hLog e)
    _ = (2 * A * 2 ^ e) * (ledger p + 1) * (logarithm model p) ^ e := by rw [mul_pow]; ring

end Blotto.GeneralPaperMeasuredUnequalInitializationRates
