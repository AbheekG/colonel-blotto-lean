import Blotto.GeneralPaperSignedCellHistory

/-! One battlefield's four cached query plans. The unsigned cross-payoff
queries use the opposite unsigned block; the signed update uses its own
unsigned block and the selected row. Preparation is outside the round loop.
-/
namespace Blotto.GeneralPaperEpochFieldPlan
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
set_option autoImplicit false

structure Plan (k : ℕ) where
  alphabet : ℕ
  candidateCount : ℕ
  responseCount : ℕ
  pSummary : Summary k
  qSummary : Summary k
  lambdaSummary : Summary k
  muSummary : Summary k
  candidateOptions : FixedArrayTable candidateCount ℕ
  responseOptions : FixedArrayTable responseCount ℕ
  pCells : GeneralPaperUnsignedCellUpdates.Plan k
  qCells : GeneralPaperUnsignedCellUpdates.Plan k
  lambdaCells : GeneralPaperSignedCellUpdates.Plan k
  muCells : GeneralPaperSignedCellUpdates.Plan k
  pOccurrences : GeneralPaperQueryLossCounts.Plan k (GeneralPaperSourceParameters.prepare k).summarySize
  qOccurrences : GeneralPaperQueryLossCounts.Plan k (GeneralPaperSourceParameters.prepare k).summarySize
  lambdaOccurrences : GeneralPaperSignedUpdatePlan.Plan k (GeneralPaperSourceParameters.prepare k).summarySize
  muOccurrences : GeneralPaperSignedUpdatePlan.Plan k (GeneralPaperSourceParameters.prepare k).summarySize
  pCells_spec : pCells=GeneralPaperUnsignedCellUpdates.prepare k alphabet qSummary lambdaSummary candidateOptions
  qCells_spec : qCells=GeneralPaperUnsignedCellUpdates.prepare k alphabet pSummary muSummary responseOptions
  lambdaCells_spec : lambdaCells=GeneralPaperSignedCellUpdates.prepare k alphabet pSummary candidateOptions
  muCells_spec : muCells=GeneralPaperSignedCellUpdates.prepare k alphabet qSummary responseOptions
  pOccurrences_spec : pOccurrences=GeneralPaperQueryLossCounts.prepare k alphabet qSummary lambdaSummary pSummary
  qOccurrences_spec : qOccurrences=GeneralPaperQueryLossCounts.prepare k alphabet pSummary muSummary qSummary
  lambdaOccurrences_spec : lambdaOccurrences=GeneralPaperSignedUpdatePlan.prepare k alphabet pSummary lambdaSummary
  muOccurrences_spec : muOccurrences=GeneralPaperSignedUpdatePlan.prepare k alphabet qSummary muSummary

def prepare {mx my : ℕ} (k U : ℕ) (p q lambda mu : Summary k)
    (candidateOptions : FixedArrayTable mx ℕ) (responseOptions : FixedArrayTable my ℕ) : Plan k :=
  ⟨U,mx,my,p,q,lambda,mu,candidateOptions,responseOptions,
    GeneralPaperUnsignedCellUpdates.prepare k U q lambda candidateOptions,
    GeneralPaperUnsignedCellUpdates.prepare k U p mu responseOptions,
    GeneralPaperSignedCellUpdates.prepare k U p candidateOptions,
    GeneralPaperSignedCellUpdates.prepare k U q responseOptions,
    GeneralPaperQueryLossCounts.prepare k U q lambda p,
    GeneralPaperQueryLossCounts.prepare k U p mu q,
    GeneralPaperSignedUpdatePlan.prepare k U p lambda,
    GeneralPaperSignedUpdatePlan.prepare k U q mu,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def CodesValid {k : ℕ} (plan : Plan k) : Prop :=
  (∀ r, plan.pSummary.read r<plan.alphabet) ∧ (∀ r, plan.qSummary.read r<plan.alphabet) ∧
  (∀ r, plan.lambdaSummary.read r<2*plan.alphabet) ∧ (∀ r, plan.muSummary.read r<2*plan.alphabet) ∧
  (∀ r, plan.candidateOptions.read r<plan.alphabet) ∧ (∀ r, plan.responseOptions.read r<plan.alphabet)

def Ordered {k : ℕ} (plan : Plan k) : Prop :=
  Monotone plan.pSummary.read ∧ Monotone plan.qSummary.read ∧
    Monotone plan.lambdaSummary.read ∧ Monotone plan.muSummary.read

def Constructed {k : ℕ} (plan : Plan k) : Prop :=
  plan=prepare k plan.alphabet plan.pSummary plan.qSummary plan.lambdaSummary plan.muSummary
    plan.candidateOptions plan.responseOptions

theorem prepare_constructed {mx my : ℕ} (k U : ℕ) (p q lambda mu : Summary k)
    (candidateOptions : FixedArrayTable mx ℕ) (responseOptions : FixedArrayTable my ℕ) :
    Constructed (prepare k U p q lambda mu candidateOptions responseOptions) := rfl

end Blotto.GeneralPaperEpochFieldPlan
