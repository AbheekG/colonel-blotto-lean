import Blotto.GeneralPaperFirstSharedBitCalibration

/-! Canonical original-input laws and every-output budgets for the
corrected equal stored branch and unchanged one-field/unequal branches.
Source records are erased observers; draws use the actual stored sampler. -/
namespace Blotto.GeneralPaperFirstAllBitLaw
open GeneralPaperOriginalGameInput
open GeneralPaperAllBranchBitDispatch (Prepared)
open GeneralPaperEqualBitBranchDraw (Trace)
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def equalSource (model : RationalCostModel) (K : ℕ) (p : Input) :=
  (GeneralPaperEqualFirstInputPipeline.run model 1 K (equalInput model p)).1

noncomputable def law (model : RationalCostModel) (K : ℕ) (p : Input) : Prepared p.n → Bool → Mixed p.n
  | .equal A output,_ => GeneralPaperStoredSelectedLaw.outputLaw model A output (equalSource model K p).branch
  | output,poor => GeneralPaperAllBranchBitLaw.law model K p output poor

def Guarantee (model : RationalCostModel) (K : ℕ) (p : Input) (output : Prepared p.n) : Prop :=
  let rich := law model K p output false
  let poor := law model K p output true
  Supported 1 rich ∧ Supported (p.budget : ℝ) poor ∧
    regret p.selector.values 1 rich poor ≤ (epsilon p : ℝ) ∧
    regret p.selector.values (p.budget : ℝ) poor rich ≤ (epsilon p : ℝ)

def Pointwise (model : RationalCostModel) (K : ℕ) (p : Input) : Prepared p.n → Prop
  | .equal A output => ∀ (trace : Trace (equalSource model K p).branch) (row : Array ℚ),
      (GeneralPaperStoredSelectedLaw.observed model A output (equalSource model K p).branch trace).output=some row →
      row.size=p.n ∧ FullBudget 1 (fun j : Fin p.n => (row.getD j.val 0 : ℝ)) ∧
        FullBudget (p.budget : ℝ) (fun j : Fin p.n => (row.getD j.val 0 : ℝ))
  | output => GeneralPaperAllBranchBitOutput.Pointwise model K p output

end Blotto.GeneralPaperFirstAllBitLaw
