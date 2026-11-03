import Blotto.GeneralPaperEqualSelectedClosureRates

/-! The old complete dispatch phases and the newly executed local closure
share one preparation word. Earlier retained owners remain live during
closure children, final increment and return. New pipeline price/control
fields are reserved through every phase. -/
namespace Blotto.GeneralPaperEqualSelectedPreparationResources
open GeneralPaperEqualInputDomain GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

def branch (model : RationalCostModel) (W : ℕ) (p : Input model) :=
  (GeneralPaperEqualBitDispatch.run model W W p.k p.values p.selector p.correct p.budget).1
def closure (model : RationalCostModel) (W : ℕ) (p : Input model) :=
  GeneralPaperEqualSelectedSampler.close model W p.k p.budget (branch model W p)
def sourceTotal (model : RationalCostModel) (W K : ℕ) (p : Input model) : ℕ :=
  (GeneralPaperEqualInputInitialization.prepareReference model W K p).2 +
    GeneralPaperEqualDispatchLifetime.sourceWork model W p + (closure model W p).2

def parentCap (model : RationalCostModel) (W K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualDispatchLifetime.parentCap model W K p +
    GeneralPaperEqualSelectedClosureWork.price model W p.n p.k (rationalWordWidth p.budget) + 1
def parentWindow (model : RationalCostModel) (W K : ℕ) (p : Input model) : ℕ :=
  fields W [p.n,p.k,W,K,(GeneralPaperEqualInputInitialization.prepareReference model W K p).2,
    GeneralPaperEqualDispatchLifetime.sourceWork model W p,(closure model W p).2,sourceTotal model W K p] + 192 * W
def parentProfile (model : RationalCostModel) (W K : ℕ) (p : Input model) : ℕ :=
  8 * (natBits (parentCap model W K p) + W) + 224 * W

theorem parent_bound (model : RationalCostModel) (W K : ℕ) (p : Input model) :
    parentWindow model W K p ≤ parentProfile model W K p := by
  have hi := GeneralPaperEqualInputInitialization.initialization_work model W K p
  have hb : GeneralPaperEqualDispatchLifetime.sourceWork model W p ≤
      GeneralPaperEqualBitDispatch.bound model W W p.k p.values p.budget :=
    GeneralPaperEqualBitDispatch.work model W W p.k p.values p.selector p.correct p.budget
  have hc : (closure model W p).2 ≤ GeneralPaperEqualSelectedClosureWork.price model W p.n p.k (rationalWordWidth p.budget) :=
    GeneralPaperEqualSelectedClosureWork.work model W p.k p.budget (branch model W p)
  have hf := fields_bound W (natBits (parentCap model W K p))
    [p.n,p.k,W,K,(GeneralPaperEqualInputInitialization.prepareReference model W K p).2,
      GeneralPaperEqualDispatchLifetime.sourceWork model W p,(closure model W p).2,sourceTotal model W K p] (by
        intro x hx; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals dsimp only [parentCap,GeneralPaperEqualDispatchLifetime.parentCap,sourceTotal]; omega)
  change fields W _ ≤ 8 * (natBits (parentCap model W K p) + W) + 32 * W at hf
  dsimp only [parentWindow,parentProfile]
  omega

noncomputable def profile (model : RationalCostModel) (W K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualDispatchLifetime.profile model W K p +
    GeneralPaperEqualSelectedClosureLifetime.profile model W p.n p.k (rationalWordWidth p.budget) + parentProfile model W K p

def Phase (model : RationalCostModel) (W : ℕ) (p : Input model) :=
  Sum (GeneralPaperEqualDispatchLifetime.Phase model W p) GeneralPaperEqualSelectedClosureLifetime.Phase

noncomputable def window (model : RationalCostModel) (W K : ℕ) (p : Input model) : Phase model W p → ℕ
  | .inl phase => GeneralPaperEqualDispatchLifetime.window model W K p phase + parentWindow model W K p
  | .inr phase => GeneralPaperEqualDispatchLifetime.window model W K p .returned +
      GeneralPaperEqualSelectedClosureLifetime.window model W p.k p.budget (branch model W p) phase + parentWindow model W K p

theorem all_phases (model : RationalCostModel) (W K : ℕ) (p : Input model)
    (hW : 1 ≤ W) (hIndex : binaryWordWidth (p.n + 1) ≤ W) (phase : Phase model W p) :
    window model W K p phase ≤ profile model W K p := by
  have hParent := parent_bound model W K p
  cases phase with
  | inl phase =>
    have h := GeneralPaperEqualDispatchLifetime.all_phases model W K p hW hIndex phase
    dsimp only [window,profile]; omega
  | inr phase =>
    have hOld := GeneralPaperEqualDispatchLifetime.all_phases model W K p hW hIndex .returned
    have hClose := GeneralPaperEqualSelectedClosureLifetime.all_phases model W W p.k p.values p.selector p.correct p.budget
      (branch model W p) phase
    dsimp only [window,profile]; omega

theorem actual_return (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    (GeneralPaperEqualSelectedPipeline.run model A K p).1 = (closure model (word K p) p).1 :=
  GeneralPaperEqualSelectedPipeline.data model A K p

theorem actual_work (model : RationalCostModel) (K : ℕ) (p : Input model) :
    (GeneralPaperEqualSelectedPipeline.run model (word K p) K p).2 = sourceTotal model (word K p) K p := by
  rw [GeneralPaperEqualSelectedPipeline.work]
  dsimp only [GeneralPaperEqualSelectedPipeline.dispatchClose,sourceTotal,closure,branch,
    GeneralPaperEqualDispatchLifetime.sourceWork]
  omega

end Blotto.GeneralPaperEqualSelectedPreparationResources
