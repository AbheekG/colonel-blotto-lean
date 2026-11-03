import Blotto.GeneralPaperRetainedCompilerBranchBits
import Blotto.GeneralPaperRetainedModifiedColumns

/-! The bit compiler's actual return materializes endpoint anchors once
and retains original stored labels. Rejected branches build no anchors. -/
namespace Blotto.GeneralPaperRetainedModifiedColumnBits
open GeneralPaperSourceEndpointBranch GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 4500000

def run {T m K : ℕ} (model : RationalCostModel) (W depth S H p q : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (ownBudget opposingProxy : ℚ)
    (reciprocal : Bool) (endpoint : Farey.Fraction) (value : ℚ) :
    Option (FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))×ℕ :=
  let branch := GeneralPaperRetainedCompilerBranchBits.run model W depth S H p q hK columns values ownBudget opposingProxy reciprocal endpoint value
  match branch.1 with
  | none => (none,branch.2+32*W)
  | some result =>
    let prepared := GeneralPaperNativeEndpointColumns.run model.rat (fun w => w) W result.choice columns
    (some prepared.1,branch.2+prepared.2+64*W)

theorem run_data {T m K : ℕ} (model : RationalCostModel) (W depth S H p q : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (ownBudget opposingProxy : ℚ)
    (reciprocal : Bool) (endpoint : Farey.Fraction) (value : ℚ) :
    (run model W depth S H p q hK columns values ownBudget opposingProxy reciprocal endpoint value).1=
      (GeneralPaperRetainedCompilerBranchBits.run model W depth S H p q hK columns values ownBudget opposingProxy reciprocal endpoint value).1.map
        (fun result => (GeneralPaperNativeEndpointColumns.run model.rat (fun w => w) W result.choice columns).1) := by
  cases hr : (GeneralPaperRetainedCompilerBranchBits.run model W depth S H p q hK columns values ownBudget opposingProxy reciprocal endpoint value).1 <;>
    simp only [run,hr,Option.map_none,Option.map_some]

theorem old_data {T m K : ℕ} (model : RationalCostModel) (depth S H p q : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (ownBudget opposingProxy : ℚ)
    (reciprocal : Bool) (endpoint : Farey.Fraction) (value : ℚ) :
    (GeneralPaperRetainedModifiedColumns.run model depth S H p q hK columns values ownBudget opposingProxy reciprocal endpoint value).1=
      (GeneralPaperRetainedCompilerBranch.run model depth S H p q hK columns values ownBudget opposingProxy reciprocal endpoint value).1.map
        (fun result => (GeneralPaperNativeEndpointColumns.run (fun _ => 1) (fun _ => 1) 1 result.choice columns).1) := by
  cases hr : (GeneralPaperRetainedCompilerBranch.run model depth S H p q hK columns values ownBudget opposingProxy reciprocal endpoint value).1 <;>
    simp only [GeneralPaperRetainedModifiedColumns.run,hr,Option.map_none,Option.map_some]

theorem data {T m : ℕ} (model : RationalCostModel) (W k p q : ℕ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T (prepare m k).K))
    (values : GeneralPaperRetainedFieldValues.Values m) (ownBudget opposingProxy : ℚ)
    (reciprocal : Bool) (endpoint : Farey.Fraction) (value : ℚ) (hValue : endpoint.value=value)
    (hm : 0<m) (hp : 0<p) (hq : 0<q) :
    (run model W (GeneralPaperScoreScaleParameters.prepare m k).depth (prepare m k).S (prepare m k).H p q
      (GeneralPaperScoreScaleParameters.labels_positive m k) columns values ownBudget opposingProxy reciprocal endpoint value).1=
      (GeneralPaperRetainedModifiedColumns.run model (GeneralPaperScoreScaleParameters.prepare m k).depth
        (prepare m k).S (prepare m k).H p q (GeneralPaperScoreScaleParameters.labels_positive m k)
        columns values ownBudget opposingProxy reciprocal endpoint value).1 := by
  have hb := GeneralPaperRetainedCompilerBranchBits.data model W k p q columns values ownBudget opposingProxy
    reciprocal endpoint value hValue hm hp hq
  erw [run_data,old_data]
  erw [hb]
  congr 1
  funext result
  exact GeneralPaperRetainedBitData.endpoint_columns model.rat (fun _ => 1) (fun w => w) (fun _ => 1) W 1 result.choice columns

def columnProfile (model : RationalCostModel) (W m K : ℕ) : ℕ :=
  m*(K*(9*model.rat (GeneralPaperNativeEndpointAnchor.width m K)+128*W)+44*(K+1)*W+64*W)+44*(m+1)*W

theorem work {T m K : ℕ} (model : RationalCostModel) (W depth S H p q : ℕ) (hK : 0<K)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (values : GeneralPaperRetainedFieldValues.Values m) (ownBudget opposingProxy : ℚ)
    (reciprocal : Bool) (endpoint : Farey.Fraction) (value : ℚ) (hW : 1≤W)
    (hIndex : binaryWordWidth (m+K+1)≤W) :
    (run model W depth S H p q hK columns values ownBudget opposingProxy reciprocal endpoint value).2≤
      (GeneralPaperRetainedCompilerBranchBits.run model W depth S H p q hK columns values ownBudget opposingProxy reciprocal endpoint value).2+
        columnProfile model W m K+64*W := by
  cases hr : (GeneralPaperRetainedCompilerBranchBits.run model W depth S H p q hK columns values ownBudget opposingProxy reciprocal endpoint value).1 with
  | none => simp only [run,hr]; omega
  | some result =>
    have hh := GeneralPaperNativeEndpointColumns.work model.rat (fun w => w) model.monotone W hW result.choice columns
      (fun i hi => (binaryWordWidth_mono (show i+1≤m+K+1 by omega)).trans hIndex)
    change _≤columnProfile model W m K at hh
    simp only [run,hr]
    omega

end Blotto.GeneralPaperRetainedModifiedColumnBits
