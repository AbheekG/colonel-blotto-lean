import Blotto.GeneralPaperEqualSelectedDescription

/-! Every operation of local closure construction is priced: pure budget
length, local reference arithmetic, final increment and returned controls.
The grouped branch reuses its already prepared reference. -/
namespace Blotto.GeneralPaperEqualSelectedClosureWork
open GeneralPaperEqualSelectedSampler
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def basePrice (model : RationalCostModel) (A n k b : ℕ) : ℕ :=
  4096 * (b + A + model.rat (GeneralPaperEqualAddressConstruction.operandWidth n 0 k b) + 1)

theorem base_work {n : ℕ} (model : RationalCostModel) (A k : ℕ) (budget : ℚ)
    {v : RationalFieldSelector n} (p : GeneralPaperEqualBitBranch.Prepared v k budget) :
    (measuredBase model A k budget p).2 ≤ basePrice model A n k (rationalWordWidth budget) := by
  cases p with
  | dominant chosen heavy row correct =>
    have hw := GeneralPaperStoredRationalWordLength.work model A budget
    have ha := GeneralPaperEqualAddressConstruction.work model A n 0 k
      (GeneralPaperStoredRationalWordLength.run model A budget).1
    rw [GeneralPaperStoredRationalWordLength.data] at ha
    have hb : binaryWordWidth (rationalWordWidth budget) + 3 ≤
        GeneralPaperEqualAddressConstruction.operandWidth n 0 k (rationalWordWidth budget) := by
      unfold GeneralPaperEqualAddressConstruction.operandWidth; omega
    have hr := model.monotone hb
    dsimp only [measuredBase,basePrice]
    rw [GeneralPaperStoredRationalWordLength.data]
    omega
  | grouped small sampler hK hB => dsimp only [measuredBase,basePrice]; omega

def price (model : RationalCostModel) (A n k b : ℕ) : ℕ :=
  basePrice model A n k b + 5 * model.rat (2 * GeneralPaperEqualBitDrawRates.log n k b + 3) + 80 * A + 80

theorem work {n : ℕ} (model : RationalCostModel) (A k : ℕ) (budget : ℚ)
    {v : RationalFieldSelector n} (p : GeneralPaperEqualBitBranch.Prepared v k budget) :
    (close model A k budget p).2 ≤ price model A n k (rationalWordWidth budget) := by
  let b := (measuredBase model A k budget p).1
  have hb : b ≤ 2 * GeneralPaperEqualBitDrawRates.log n k (rationalWordWidth budget) := by
    dsimp only [b]; rw [measured_base_data]; exact base_bound p
  have hw := GeneralPaperNaturalScalarLifetime.counter_word b
  have ho := GeneralPaperNaturalScalarLifetime.counter_word (b + 1)
  have hOne : GeneralPaperNaturalScalarStep.word 1 = 2 := by decide
  have hIncrement := GeneralPaperEqualAddressConstruction.price_work model A b 1 (b + 1)
    (2 * GeneralPaperEqualBitDrawRates.log n k (rationalWordWidth budget) + 3)
    (by change GeneralPaperEncodedScalarStorage.natBits b ≤ _; omega)
    (by rw [hOne]; omega)
    (by change GeneralPaperEncodedScalarStorage.natBits (b + 1) ≤ _; omega)
  have hBase := base_work model A k budget p
  dsimp only [close,price]
  change (measuredBase model A k budget p).2 +
    GeneralPaperEqualAddressConstruction.price model A b 1 (b + 1) + 64 * A + 64 ≤ _
  omega

theorem paper_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    GeneralPaperUniformResourceGrowth.Bound
      (fun p : GeneralPaperEqualInputDomain.Input model => price model (GeneralPaperEqualInputDomain.word K p)
        p.n p.k (rationalWordWidth p.budget))
      GeneralPaperEqualInputDomain.ledger GeneralPaperEqualInputDomain.logarithm := by
  have hL : ∀ p : GeneralPaperEqualInputDomain.Input model, 1 ≤ GeneralPaperEqualInputDomain.logarithm p :=
    GeneralPaperEqualInputDomain.logarithm_positive
  have hr : ∀ p : GeneralPaperEqualInputDomain.Input model, 1 ≤ GeneralPaperEqualInputDomain.ledger p :=
    GeneralPaperEqualInputDomain.ledger_positive
  dsimp only [price,basePrice,GeneralPaperEqualAddressConstruction.operandWidth,
    GeneralPaperEqualBitDrawRates.log,GeneralPaperEqualBitDrawRates.word,GeneralPaperEqualBitDrawRates.size]
  fun_prop (config := {maxSteps := 50000})

end Blotto.GeneralPaperEqualSelectedClosureWork
