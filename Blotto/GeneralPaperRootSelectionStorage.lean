import Blotto.GeneralPaperRootScanStorage

/-! Root selection owns one actual index list, its retained option stack,
one current eligibility tag and the literal budget tag. The root resource
word follows its subtree height; the budget word stays an explicit input.
No resource, budget or table-height calibration pass executes. -/
namespace Blotto.GeneralPaperRootSelectionStorage
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter GeneralPaperEncodedFixedVector
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def eligibleBits {Witness : Type*} {J : ℕ} (W : ℕ) (table : Table Tag Witness J) (i : Fin J) : ℕ :=
  match table.read i with
  | none => 32*W
  | some chosen => rationalWordWidth chosen.cost.threshold+1+64*W

theorem eligible_bound {Witness : Type*} {J : ℕ} (W s : ℕ) (table : Table Tag Witness J)
    (hs : GeneralPaperOrderedTableHeight.Safe s table) (i : Fin J) : eligibleBits W table i≤1+2*s+1+64*W := by
  cases hi : table.read i with
  | none => simp only [eligibleBits,hi]; omega
  | some chosen =>
    have hw := rationalWordWidth_of_height (hs i chosen hi)
    simp only [eligibleBits,hi]
    omega

def window {Witness : Type*} {J : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A : ℕ)
    (table : Table Tag Witness J) (budget : Tag) : ℕ :=
  let labelA := if bits then GeneralPaperSummaryArrayExecution.arrayWord A (J+2) else A
  let labels := (GeneralPaperDPTableControls.labels index A labelA J).1
  let callback := GeneralPaperRootEligiblePrice.run price A labelA table budget
  GeneralPaperEncodedLabelStorage.listFootprint W labels+
    GeneralPaperRootScanStorage.peak index W A (eligibleBits W table) callback labels+
    GeneralPaperRootScanStorage.optionalBits W (GeneralPaperRootSelectPrice.run bits index price A table budget).1+
    rationalWordWidth budget.threshold+1+128*W

def profile (W J s budgetWord : ℕ) : ℕ :=
  GeneralPaperDPControlStorage.labelsProfile W J+
    GeneralPaperRootScanStorage.profile W J (1+2*s+1+64*W) J+rankWord J+budgetWord+1+160*W

theorem native {Witness : Type*} {J : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A s : ℕ)
    (table : Table Tag Witness J) (budget : Tag) (hs : GeneralPaperOrderedTableHeight.Safe s table) :
    window bits index price W A table budget≤profile W J s (rationalWordWidth budget.threshold) := by
  let labelA := if bits then GeneralPaperSummaryArrayExecution.arrayWord A (J+2) else A
  let labels := (GeneralPaperDPTableControls.labels index A labelA J).1
  have hl := GeneralPaperEncodedLabelStorage.list_bound W J labels (by
    dsimp only [labels]
    rw [GeneralPaperDPTableControls.labels_data,List.length_finRange])
  have hp := GeneralPaperRootScanStorage.bounded index W A (1+2*s+1+64*W)
    (eligibleBits W table) (GeneralPaperRootEligiblePrice.run price A labelA table budget) labels
    (fun i _ => eligible_bound W s table hs i)
  have hn : labels.length=J := by dsimp only [labels]; rw [GeneralPaperDPTableControls.labels_data,List.length_finRange]
  rw [hn] at hp
  have hr := GeneralPaperRootScanStorage.optional_bound W (GeneralPaperRootSelectPrice.run bits index price A table budget).1
  unfold window profile GeneralPaperDPControlStorage.labelsProfile
  dsimp only
  dsimp only [labels,labelA] at hl hp
  omega

theorem root_candidate {K q w B h : ℕ} (W s : ℕ) (grid : GeneralPaperProfitGridPrepare.Prepared q w B)
    (tree : GeneralPaperOrderedProfitDP.Tree Tag K h) (hl : GeneralPaperOrderedDPHeight.Leaves s tree)
    (i : Fin grid.size) :
    eligibleBits W (GeneralPaperOrderedProfitDP.run grid tree).table i≤GeneralPaperTagHeight.word s h+1+64*W :=
  eligible_bound W (expressionHeightBudget s h) _ (GeneralPaperOrderedDPHeight.states grid tree s hl) i

end Blotto.GeneralPaperRootSelectionStorage
