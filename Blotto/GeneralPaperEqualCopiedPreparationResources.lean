import Blotto.GeneralPaperEqualSelectedCopyLifetimeRates

/-! Literal all-phase join for the actual initialized selected preparation,
local closure and retained copy. Earlier returned owners survive the copy;
the complete copied return and every saved pipeline price are retained. -/
namespace Blotto.GeneralPaperEqualCopiedPreparationResources
open GeneralPaperEqualInputDomain GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def source (model : RationalCostModel) (W : ℕ) (p : Input model) :=
  (GeneralPaperEqualSelectedPreparationResources.closure model W p).1
def copied (model : RationalCostModel) (W : ℕ) (p : Input model) :=
  GeneralPaperEqualSelectedCopy.run W (source model W p)
def sourceTotal (model : RationalCostModel) (W K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualSelectedPreparationResources.sourceTotal model W K p + (copied model W p).2

def parentCap (model : RationalCostModel) (W K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualSelectedPreparationResources.parentCap model W K p +
    GeneralPaperEqualSelectedCopyWork.profile W p.n p.k (rationalWordWidth p.budget) + 1

def parentWindow (model : RationalCostModel) (W K : ℕ) (p : Input model) : ℕ :=
  let dispatch := GeneralPaperEqualDispatchLifetime.sourceWork model W p
  let closure := (GeneralPaperEqualSelectedPreparationResources.closure model W p).2
  let copy := (copied model W p).2
  fields W [p.n,p.k,W,K,(GeneralPaperEqualInputInitialization.prepareReference model W K p).2,
    dispatch,closure,GeneralPaperEqualSelectedPreparationResources.sourceTotal model W K p,
    copy,dispatch+closure,dispatch+closure+copy,sourceTotal model W K p] + 256 * W

def parentProfile (model : RationalCostModel) (W K : ℕ) (p : Input model) : ℕ :=
  12 * (natBits (parentCap model W K p) + W) + 288 * W

theorem parent_bound (model : RationalCostModel) (W K : ℕ) (p : Input model) :
    parentWindow model W K p ≤ parentProfile model W K p := by
  have hi := GeneralPaperEqualInputInitialization.initialization_work model W K p
  have hb : GeneralPaperEqualDispatchLifetime.sourceWork model W p ≤
      GeneralPaperEqualBitDispatch.bound model W W p.k p.values p.budget :=
    GeneralPaperEqualBitDispatch.work model W W p.k p.values p.selector p.correct p.budget
  have hc : (GeneralPaperEqualSelectedPreparationResources.closure model W p).2 ≤
      GeneralPaperEqualSelectedClosureWork.price model W p.n p.k (rationalWordWidth p.budget) :=
    GeneralPaperEqualSelectedClosureWork.work model W p.k p.budget
      (GeneralPaperEqualSelectedPreparationResources.branch model W p)
  have hCopy : (copied model W p).2 ≤ GeneralPaperEqualSelectedCopyWork.profile W p.n p.k (rationalWordWidth p.budget) :=
    GeneralPaperEqualSelectedCopyWork.work model W W p.k p.values p.selector p.correct p.budget (source model W p)
  have hf := fields_bound W (natBits (parentCap model W K p))
    [p.n,p.k,W,K,(GeneralPaperEqualInputInitialization.prepareReference model W K p).2,
      GeneralPaperEqualDispatchLifetime.sourceWork model W p,(GeneralPaperEqualSelectedPreparationResources.closure model W p).2,
      GeneralPaperEqualSelectedPreparationResources.sourceTotal model W K p,(copied model W p).2,
      GeneralPaperEqualDispatchLifetime.sourceWork model W p + (GeneralPaperEqualSelectedPreparationResources.closure model W p).2,
      GeneralPaperEqualDispatchLifetime.sourceWork model W p + (GeneralPaperEqualSelectedPreparationResources.closure model W p).2 +
        (copied model W p).2,sourceTotal model W K p] (by
        intro x hx
        apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
        all_goals dsimp only [parentCap,GeneralPaperEqualSelectedPreparationResources.parentCap,
          GeneralPaperEqualDispatchLifetime.parentCap,sourceTotal,GeneralPaperEqualSelectedPreparationResources.sourceTotal]; omega)
  change fields W _ ≤ 12 * (natBits (parentCap model W K p) + W) + 32 * W at hf
  dsimp only [parentWindow,parentProfile]
  omega

noncomputable def profile (model : RationalCostModel) (W K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualSelectedPreparationResources.profile model W K p +
    GeneralPaperEqualSelectedCopyLifetime.profile W p.n p.k (rationalWordWidth p.budget) + parentProfile model W K p

inductive Phase (model : RationalCostModel) (W : ℕ) (p : Input model) where
  | preparation (phase : GeneralPaperEqualSelectedPreparationResources.Phase model W p)
  | copying (cursor : GeneralPaperEqualSelectedCopyComponents.Cursor (source model W p))
  | returned

noncomputable def window (model : RationalCostModel) (W K : ℕ) (p : Input model) : Phase model W p → ℕ
  | .preparation phase => GeneralPaperEqualSelectedPreparationResources.window model W K p phase + parentWindow model W K p
  | .copying cursor => GeneralPaperEqualSelectedPreparationResources.window model W K p (.inr .returned) +
    GeneralPaperEqualSelectedCopyLifetime.window W (source model W p) cursor + parentWindow model W K p
  | .returned => GeneralPaperEqualSelectedPreparationResources.window model W K p (.inr .returned) +
    GeneralPaperEqualSelectedDescription.footprint (copied model W p).1 + parentWindow model W K p

theorem all_phases (model : RationalCostModel) (W K : ℕ) (p : Input model)
    (hW : 1 ≤ W) (hIndex : binaryWordWidth (p.n + 1) ≤ W) (phase : Phase model W p) :
    window model W K p phase ≤ profile model W K p := by
  have hParent := parent_bound model W K p
  cases phase with
  | preparation phase =>
    have hOld := GeneralPaperEqualSelectedPreparationResources.all_phases model W K p hW hIndex phase
    dsimp only [window,profile]
    omega
  | copying cursor =>
    have hOld := GeneralPaperEqualSelectedPreparationResources.all_phases model W K p hW hIndex (.inr .returned)
    have hCopy := GeneralPaperEqualSelectedCopyLifetime.all_cursors model W W p.k p.values p.selector p.correct p.budget
      (source model W p) cursor
    dsimp only [window,profile]
    omega
  | returned =>
    have hOld := GeneralPaperEqualSelectedPreparationResources.all_phases model W K p hW hIndex (.inr .returned)
    have hTarget := GeneralPaperEqualSelectedDescription.paper_bound model W p.k p.values p.selector p.correct p.budget
      (copied model W p).1
    have hCopy : GeneralPaperEqualSelectedDescription.footprint (copied model W p).1 ≤
        GeneralPaperEqualSelectedCopyLifetime.profile W p.n p.k (rationalWordWidth p.budget) := by
      unfold GeneralPaperEqualSelectedCopyLifetime.profile
      omega
    dsimp only [window,profile]
    omega

theorem actual_return (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    (GeneralPaperEqualCopiedPipeline.run model A K p).1 = (copied model (word K p) p).1 := by
  rw [GeneralPaperEqualCopiedPipeline.data]
  rfl

theorem actual_work (model : RationalCostModel) (K : ℕ) (p : Input model) :
    (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).2 = sourceTotal model (word K p) K p := by
  rw [GeneralPaperEqualCopiedPipeline.copy_work_exact,GeneralPaperEqualSelectedPreparationResources.actual_work,
    GeneralPaperEqualSelectedPreparationResources.actual_return]
  rfl

end Blotto.GeneralPaperEqualCopiedPreparationResources
