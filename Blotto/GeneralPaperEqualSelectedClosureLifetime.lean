import Blotto.GeneralPaperEqualSelectedBranchOwner

/-! Literal local closure phases. Pure budget/address children reuse their
complete checked recursive/operand observers. The final increment has its
own scalar scratch. Actual base/partial-work pairs, caller controls, selected
branch owner and complete returned mixed-width closure stay reserved. -/
namespace Blotto.GeneralPaperEqualSelectedClosureLifetime
open GeneralPaperEqualSelectedSampler GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

inductive Phase where
  | budgetWords | address | increment | returned

def incrementPrice {n : ℕ} (model : RationalCostModel) (W k : ℕ) (budget : ℚ)
    {v : RationalFieldSelector n} (p : GeneralPaperEqualBitBranch.Prepared v k budget) : ℕ :=
  let base := (measuredBase model W k budget p).1
  GeneralPaperEqualAddressConstruction.price model W base 1 (base + 1)

theorem source_work {n : ℕ} (model : RationalCostModel) (W k : ℕ) (budget : ℚ)
    {v : RationalFieldSelector n} (p : GeneralPaperEqualBitBranch.Prepared v k budget) :
    (close model W k budget p).2 = (measuredBase model W k budget p).2 +
      incrementPrice model W k budget p + 64 * W + 64 := rfl

def controlCap (model : RationalCostModel) (W n k b : ℕ) : ℕ :=
  n + k + b + 2 * GeneralPaperEqualBitDrawRates.log n k b +
    GeneralPaperEqualSelectedClosureWork.price model W n k b + 128 * W + 128

def baseControls {n : ℕ} (model : RationalCostModel) (W k : ℕ) (budget : ℚ)
    {v : RationalFieldSelector n} : GeneralPaperEqualBitBranch.Prepared v k budget → List ℕ
  | .dominant _ _ _ _ =>
    let word := GeneralPaperStoredRationalWordLength.run model W budget
    let address := GeneralPaperEqualAddressConstruction.run model W n 0 k word.1
    [word.1,word.2,address.1,address.2,word.2 + address.2]
  | .grouped _ sampler _ _ => [sampler.address,32 * W + 32]

def controls {n : ℕ} (model : RationalCostModel) (W k : ℕ) (budget : ℚ)
    {v : RationalFieldSelector n} (p : GeneralPaperEqualBitBranch.Prepared v k budget) : ℕ :=
  let base := measuredBase model W k budget p
  let actual := close model W k budget p
  let inc := incrementPrice model W k budget p
  fields W [n,k,base.1,base.2,actual.1.address,inc,actual.2,base.2 + inc] +
    fields W (baseControls model W k budget p) + 192 * W

def controlProfile (model : RationalCostModel) (W n k b : ℕ) : ℕ :=
  13 * (natBits (controlCap model W n k b) + W) + 256 * W

theorem base_controls_bound {n : ℕ} (model : RationalCostModel) (W k : ℕ) (budget : ℚ)
    {v : RationalFieldSelector n} (p : GeneralPaperEqualBitBranch.Prepared v k budget) :
    ∀ x ∈ baseControls model W k budget p, x ≤ controlCap model W n k (rationalWordWidth budget) := by
  have hw := GeneralPaperEqualSelectedClosureWork.work model W k budget p
  have hb : (measuredBase model W k budget p).2 ≤ GeneralPaperEqualSelectedClosureWork.price model W n k (rationalWordWidth budget) := by
    rw [source_work] at hw; omega
  have ho : (measuredBase model W k budget p).1 ≤ 2 * GeneralPaperEqualBitDrawRates.log n k (rationalWordWidth budget) := by
    rw [measured_base_data]; exact base_bound p
  cases p with
  | dominant chosen heavy row correct =>
    have hWord := GeneralPaperStoredRationalWordLength.data model W budget
    dsimp only [measuredBase] at hb ho
    intro x hx
    simp only [baseControls,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    all_goals unfold controlCap; omega
  | grouped small sampler hK hB =>
    dsimp only [measuredBase] at hb ho
    intro x hx
    simp only [baseControls,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl
    all_goals unfold controlCap; omega

theorem controls_bound {n : ℕ} (model : RationalCostModel) (W k : ℕ) (budget : ℚ)
    {v : RationalFieldSelector n} (p : GeneralPaperEqualBitBranch.Prepared v k budget) :
    controls model W k budget p ≤ controlProfile model W n k (rationalWordWidth budget) := by
  have hw := GeneralPaperEqualSelectedClosureWork.work model W k budget p
  have hs := source_work model W k budget p
  have ho : (measuredBase model W k budget p).1 ≤ 2 * GeneralPaperEqualBitDrawRates.log n k (rationalWordWidth budget) := by
    rw [measured_base_data]; exact base_bound p
  have hA : (close model W k budget p).1.address = (measuredBase model W k budget p).1 + 1 := rfl
  have hf := fields_bound W (natBits (controlCap model W n k (rationalWordWidth budget)))
    [n,k,(measuredBase model W k budget p).1,(measuredBase model W k budget p).2,
      (close model W k budget p).1.address,incrementPrice model W k budget p,
      (close model W k budget p).2,(measuredBase model W k budget p).2 + incrementPrice model W k budget p] (by
      intro x hx; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals unfold controlCap; omega)
  change fields W _ ≤ 8 * (natBits (controlCap model W n k (rationalWordWidth budget)) + W) + 32 * W at hf
  have hb := fields_bound W (natBits (controlCap model W n k (rationalWordWidth budget))) (baseControls model W k budget p)
    (fun x hx => Nat.add_le_add_left (binaryWordWidth_mono (base_controls_bound model W k budget p x hx)) 1)
  have hLen : (baseControls model W k budget p).length ≤ 5 := by
    cases p <;> simp only [baseControls,List.length_cons,List.length_nil] <;> omega
  have hBase := hb.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hLen) (32 * W))
  dsimp only [controls,controlProfile]
  omega

def component {n : ℕ} (model : RationalCostModel) (W k : ℕ) (budget : ℚ)
    {v : RationalFieldSelector n} (p : GeneralPaperEqualBitBranch.Prepared v k budget) : Phase → ℕ
  | .budgetWords => match p with
    | .dominant _ _ _ _ => GeneralPaperWordLengthLifetime.rationalFoot model W budget
    | .grouped _ _ _ _ => 0
  | .address => match p with
    | .dominant _ _ _ _ => GeneralPaperAddressConstructionLifetime.footprint model W n 0 k
        (GeneralPaperStoredRationalWordLength.run model W budget).1
    | .grouped _ _ _ _ => 0
  | .increment => GeneralPaperAddressConstructionLifetime.scalarFoot model W (measuredBase model W k budget p).1 1
      ((measuredBase model W k budget p).1 + 1)
  | .returned => 0

def componentProfile (model : RationalCostModel) (W n k b : ℕ) : ℕ :=
  GeneralPaperWordLengthLifetime.rationalProfile model W b +
    GeneralPaperAddressConstructionLifetime.profile model W n 0 k b +
    32 * GeneralPaperEqualSelectedClosureWork.price model W n k b

theorem component_bound {n : ℕ} (model : RationalCostModel) (W k : ℕ) (budget : ℚ)
    {v : RationalFieldSelector n} (p : GeneralPaperEqualBitBranch.Prepared v k budget) (phase : Phase) :
    component model W k budget p phase ≤ componentProfile model W n k (rationalWordWidth budget) := by
  cases phase with
  | budgetWords =>
    have h := GeneralPaperWordLengthLifetime.rational_input_bound model W budget
    cases p <;> dsimp only [component,componentProfile] <;> omega
  | address =>
    have h := GeneralPaperAddressConstructionLifetime.input_bound model W n 0 k (rationalWordWidth budget)
    cases p <;> dsimp only [component,componentProfile]
    · rw [GeneralPaperStoredRationalWordLength.data]; omega
    · omega
  | increment =>
    have h := GeneralPaperAddressConstructionLifetime.scalar_bound model W (measuredBase model W k budget p).1 1
      ((measuredBase model W k budget p).1 + 1)
    change component model W k budget p .increment ≤ 32 * incrementPrice model W k budget p at h
    have hw := GeneralPaperEqualSelectedClosureWork.work model W k budget p
    rw [source_work] at hw
    dsimp only [componentProfile]
    omega
  | returned => dsimp only [component,componentProfile]; omega

def window {n : ℕ} (model : RationalCostModel) (W k : ℕ) (budget : ℚ)
    {v : RationalFieldSelector n} (p : GeneralPaperEqualBitBranch.Prepared v k budget) (phase : Phase) : ℕ :=
  GeneralPaperEqualSelectedBranchOwner.footprint W p + controls model W k budget p + component model W k budget p phase +
    GeneralPaperEqualSelectedDescription.footprint (close model W k budget p).1

def profile (model : RationalCostModel) (W n k b : ℕ) : ℕ :=
  GeneralPaperEqualSelectedBranchOwner.profile W n k b + controlProfile model W n k b + componentProfile model W n k b +
    2 * GeneralPaperEqualDescriptionRates.paperBound n k b

theorem all_phases {n : ℕ} (model : RationalCostModel) (Wv W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (p : GeneralPaperEqualBitBranch.Prepared
      (GeneralPaperEqualNativeSampler.rounded true model Wv k values v hv) k budget) (phase : Phase) :
    window model W k budget p phase ≤ profile model W n k (rationalWordWidth budget) := by
  have ho := GeneralPaperEqualSelectedBranchOwner.bounded model Wv W k values v hv budget p
  have hc := controls_bound model W k budget p
  have hs := component_bound model W k budget p phase
  have hr := GeneralPaperEqualSelectedDescription.paper_bound model Wv k values v hv budget (close model W k budget p).1
  dsimp only [window,profile]
  omega

end Blotto.GeneralPaperEqualSelectedClosureLifetime
