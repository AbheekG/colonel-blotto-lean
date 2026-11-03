import Blotto.GeneralPaperRetainedCompilerSource

/-! Materialize physical endpoint anchors from the actual once-only
retained compiler return, preserving the source's stored label arrays.
No output anchors are built when the branch returns none. -/
namespace Blotto.GeneralPaperRetainedModifiedColumns
open GeneralPaperSourceEndpointBranch
set_option autoImplicit false
set_option maxHeartbeats 3500000

def run {T m K : ℕ} (model : RationalCostModel) (depth S H p q : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (ownBudget opposingProxy : ℚ)
    (reciprocal : Bool) (endpoint : Farey.Fraction) (value : ℚ) :
    Option (FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))×ℕ :=
  let branch := GeneralPaperRetainedCompilerBranch.run model depth S H p q hK columns values ownBudget opposingProxy reciprocal endpoint value
  match branch.1 with
  | none => (none,branch.2+32)
  | some result =>
    let prepared := GeneralPaperNativeEndpointColumns.run (fun _ => 1) (fun _ => 1) 1 result.choice columns
    (some prepared.1,branch.2+prepared.2+64)

theorem data {T m K : ℕ} (model : RationalCostModel) (depth S H p q : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (ownBudget opposingProxy : ℚ)
    (reciprocal : Bool) (endpoint : Farey.Fraction) (value : ℚ) :
    (run model depth S H p q hK columns values ownBudget opposingProxy reciprocal endpoint value).1.map GeneralPaperRowQuantizer.dictionary=
      (GeneralPaperRetainedCompilerBranch.run model depth S H p q hK columns values ownBudget opposingProxy reciprocal endpoint value).1.map
        GeneralPaperEndpointDictionary.dictionary := by
  cases hr : (GeneralPaperRetainedCompilerBranch.run model depth S H p q hK columns values ownBudget opposingProxy reciprocal endpoint value).1 with
  | none => simp only [run,hr,Option.map_none]
  | some result =>
    simp only [run,hr,Option.map_some]
    exact congrArg some (GeneralPaperNativeEndpointColumnLaw.result_data _ _ _ result columns
      (GeneralPaperRetainedCompilerBranch.labels model depth S H p q hK columns values ownBudget opposingProxy reciprocal endpoint value result hr))

theorem arithmetic_work {T m K : ℕ} (model : RationalCostModel) (depth S H p q : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (ownBudget opposingProxy : ℚ)
    (reciprocal : Bool) (endpoint : Farey.Fraction) (value : ℚ) :
    (run model depth S H p q hK columns values ownBudget opposingProxy reciprocal endpoint value).2≤
      (GeneralPaperRetainedCompilerBranch.run model depth S H p q hK columns values ownBudget opposingProxy reciprocal endpoint value).2+
        m*(K*137+44*(K+1)+64)+44*(m+1)+64 := by
  cases hr : (GeneralPaperRetainedCompilerBranch.run model depth S H p q hK columns values ownBudget opposingProxy reciprocal endpoint value).1 with
  | none => simp only [run,hr];omega
  | some result =>
    have hh := GeneralPaperNativeEndpointColumns.work (fun _ => 1) (fun _ => 1) (fun _ _ _ => le_rfl)
      1 (by decide) result.choice columns (fun _ _ => le_rfl)
    norm_num only [Nat.mul_one,Nat.reduceAdd] at hh
    simp only [run,hr]
    omega

end Blotto.GeneralPaperRetainedModifiedColumns
