import Blotto.BinaryOneFieldBoundary

/-! The paper one-field endpoint joins exact continuous equilibrium with
the actual unchanged stored-budget output frames and their visit bound.
No random bits or arithmetic encoding of the budget is required. -/
namespace Blotto.GeneralPaperOneFieldContract
open BinaryRationalNormalization BinaryRationalEncoding BinaryOneFieldBoundary
set_option autoImplicit false

theorem actual_output_contract (values : Values 1) (a b : SignedWord)
    (ha : BinaryRationalOpcode.Valid a) (hb : BinaryRationalOpcode.Valid b)
    (ha0 : 0 ≤ value a) (hb0 : 0 ≤ value b) :
    Supported (value a : ℝ) (law a) ∧ Supported (value b : ℝ) (law b) ∧
      regret values (value a : ℝ) (law a) (law b) = 0 ∧
      regret values (value b : ℝ) (law b) (law a) = 0 ∧
      ∀ rich,
        FullBudget (value (selected rich a b) : ℝ)
          (fun j => (value ((row (selected rich a b)).read j) : ℝ)) ∧
        (outputWithWork rich a b).1 = output rich a b ∧
        (outputWithWork rich a b).2 ≤ 8 * payloadSize (selected rich a b) + 21 ∧
        ∀ suffix, BinaryRatListFrame.readRow ((outputWithWork rich a b).1 ++ suffix) =
          some (1, [value (selected rich a b)], suffix) := by
  have h := pair_equilibrium values a b ha0 hb0
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, ?_⟩
  intro rich
  refine ⟨row_fullBudget _ ?_, rfl, outputWithWork_bound rich a b, ?_⟩
  · cases rich
    · exact hb0
    · exact ha0
  · exact output_read rich a b ha hb

end Blotto.GeneralPaperOneFieldContract
