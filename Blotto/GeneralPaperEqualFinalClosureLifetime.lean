import Blotto.GeneralPaperAddressConstructionLifetime

/-! Final budget scan, address arithmetic and sampler/control return. A
proved caller supplies earlier owners and a proved reserve for the returned
sampler payload. Both remain reserved during all closure phases. -/
namespace Blotto.GeneralPaperEqualFinalClosureLifetime
open GeneralPaperEncodedScalarStorage (natBits fields)
set_option autoImplicit false
set_option maxHeartbeats 2000000

def budgetWord (model : RationalCostModel) (A : ℕ) (budget : ℚ) := GeneralPaperStoredRationalWordLength.run model A budget

def address (model : RationalCostModel) (A n m k : ℕ) (budget : ℚ) :=
  GeneralPaperEqualAddressConstruction.run model A n m k (budgetWord model A budget).1

def tailWork (model : RationalCostModel) (A n m k : ℕ) (budget : ℚ) : ℕ :=
  (budgetWord model A budget).2 + (address model A n m k budget).2 + 128 * (A + (budgetWord model A budget).1 + 1)

def time (model : RationalCostModel) (A n m k b : ℕ) : ℕ :=
  1024 * (b + A + model.rat (binaryWordWidth b + 3) + 1) +
    1024 * (model.rat (GeneralPaperEqualAddressConstruction.operandWidth n m k b) + A + 1) + 128 * (A + b + 1)

theorem tail_work (model : RationalCostModel) (A n m k : ℕ) (budget : ℚ) :
    tailWork model A n m k budget ≤ time model A n m k (rationalWordWidth budget) := by
  have hBudget := GeneralPaperStoredRationalWordLength.work model A budget
  have hAddress := GeneralPaperEqualAddressConstruction.work model A n m k (budgetWord model A budget).1
  have hData : (budgetWord model A budget).1 = rationalWordWidth budget := GeneralPaperStoredRationalWordLength.data model A budget
  rw [hData] at hAddress
  unfold tailWork time address
  rw [hData]
  exact Nat.add_le_add_right (Nat.add_le_add hBudget hAddress) _

def controls (model : RationalCostModel) (A n m k : ℕ) (budget : ℚ) : ℕ :=
  let b := budgetWord model A budget
  let a := address model A n m k budget
  fields A [k, b.1, b.2, a.1, a.2, 128 * (A + b.1 + 1), tailWork model A n m k budget] + 256 * A

def controlProfile (model : RationalCostModel) (A n m k b : ℕ) : ℕ :=
  7 * (b + time model A n m k b + 2 + A) + 288 * A

theorem controls_bound (model : RationalCostModel) (A n m k : ℕ) (budget : ℚ) :
    controls model A n m k budget ≤ controlProfile model A n m k (rationalWordWidth budget) := by
  let b := budgetWord model A budget
  let a := address model A n m k budget
  let F := tailWork model A n m k budget
  have hF : F = b.2 + a.2 + 128 * (A + b.1 + 1) := rfl
  have hTime : F ≤ time model A n m k (rationalWordWidth budget) := tail_work model A n m k budget
  have hData : b.1 = rationalWordWidth budget := GeneralPaperStoredRationalWordLength.data model A budget
  have hK := (GeneralPaperAddressConstructionLifetime.input_words model A n m k b.1).2.2.1
  change natBits k ≤ a.2 at hK
  have hAddress := GeneralPaperAddressConstructionLifetime.output_word model A n m k b.1
  change natBits a.1 ≤ a.2 at hAddress
  have hBudget := GeneralPaperNaturalScalarLifetime.counter_word b.1
  have hFields := GeneralPaperEncodedScalarStorage.fields_bound A
    (rationalWordWidth budget + time model A n m k (rationalWordWidth budget) + 2)
    [k, b.1, b.2, a.1, a.2, 128 * (A + b.1 + 1), F] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · omega
      · omega
      · exact (GeneralPaperNaturalScalarLifetime.counter_word _).trans (by omega)
      · omega
      · exact (GeneralPaperNaturalScalarLifetime.counter_word _).trans (by omega)
      · exact (GeneralPaperNaturalScalarLifetime.counter_word _).trans (by omega)
      · exact (GeneralPaperNaturalScalarLifetime.counter_word _).trans (by omega))
  change fields A _ ≤ 7 * (rationalWordWidth budget + time model A n m k (rationalWordWidth budget) + 2 + A) + 32 * A at hFields
  change fields A [k, b.1, b.2, a.1, a.2, 128 * (A + b.1 + 1), F] + 256 * A ≤ _
  unfold controlProfile
  omega

inductive Phase where
  | budgetWord
  | address
  | returned

def window (model : RationalCostModel) (A n m k : ℕ) (budget : ℚ) (borrowed returnedPayload : ℕ) (phase : Phase) : ℕ :=
  borrowed + returnedPayload + rationalWordWidth budget + controls model A n m k budget +
    match phase with
    | .budgetWord => GeneralPaperWordLengthLifetime.rationalFoot model A budget
    | .address => GeneralPaperAddressConstructionLifetime.footprint model A n m k (budgetWord model A budget).1
    | .returned => 0

def profile (model : RationalCostModel) (A n m k b borrowed returnedPayload : ℕ) : ℕ :=
  borrowed + returnedPayload + b + controlProfile model A n m k b +
    GeneralPaperWordLengthLifetime.rationalProfile model A b + GeneralPaperAddressConstructionLifetime.profile model A n m k b

theorem owner_mono (model : RationalCostModel) (A n m k b B C R S : ℕ) (hB : B ≤ C) (hR : R ≤ S) :
    profile model A n m k b B R ≤ profile model A n m k b C S := by unfold profile; omega

theorem all_phases (model : RationalCostModel) (A n m k : ℕ) (budget : ℚ) (borrowed returnedPayload : ℕ) (phase : Phase) :
    window model A n m k budget borrowed returnedPayload phase ≤
      profile model A n m k (rationalWordWidth budget) borrowed returnedPayload := by
  have hControls := controls_bound model A n m k budget
  cases phase with
  | budgetWord =>
    have hBudget := GeneralPaperWordLengthLifetime.rational_input_bound model A budget
    simp only [window]
    unfold profile
    omega
  | address =>
    have hAddress := GeneralPaperAddressConstructionLifetime.input_bound model A n m k (budgetWord model A budget).1
    rw [show (budgetWord model A budget).1 = rationalWordWidth budget from GeneralPaperStoredRationalWordLength.data model A budget] at hAddress
    simp only [window, budgetWord, GeneralPaperStoredRationalWordLength.data]
    unfold profile
    omega
  | returned =>
    simp only [window]
    unfold profile
    omega

end Blotto.GeneralPaperEqualFinalClosureLifetime
