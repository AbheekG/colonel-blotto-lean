import Blotto.GeneralPaperStoredEndpointWork
import Blotto.GeneralPaperStoredInterpolationWork
import Blotto.GeneralPaperStoredPreparedReadWork
import Blotto.GeneralPaperStoredPreparedGroups

/-! Complete actual prepared-root group production joins the original
budget read, selected endpoint reads and one interpolated group array.
Measured selected-row ownership derives the materialization index capacity. -/
namespace Blotto.GeneralPaperStoredPreparedGroupsWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperStoredReadContext (Context)
open GeneralPaperPositiveSegmentCompaction (count)
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

def bound (model : RationalCostModel) (A m s b K : ℕ) : ℕ :=
  2 * (1 + 2 * b) + GeneralPaperStoredScalarReadWork.overhead model A +
    GeneralPaperStoredReferenceReadWork.readBound model A A +
    2 * GeneralPaperStoredEndpointWork.heightBound model A m s +
    GeneralPaperStoredInterpolationWork.bound model A m (GeneralPaperEqualBitGroups.base s b K) + 512 * (A + 1)

theorem work (model : RationalCostModel) (S A layoutStart start s b : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed)
    (prepared : GeneralPaperEqualPreparedCache.Prepared G l)
    (hRead : Readback model A installed (GeneralPaperPreparedRecordCursor.expected model S A prepared start))
    (hHeaders : ∀ header ∈ (GeneralPaperPreparedRecordCursor.expected model S A prepared start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperPreparedRecordCursor.expected model S A prepared start).root.reference)
    (hs : 2 ≤ s) (h : l.HeightAt s) (hB : RationalHeight prepared.budget b)
    (index : Fin (count l)) (fresh : Fin prepared.midpointBits → Bool) :
    (GeneralPaperStoredPreparedGroups.run model A installed index.val (GeneralPaperEqualPreparedCache.midpoint prepared fresh)).2 ≤
      bound model A m s b prepared.midpointBits := by
  have hBudget := (GeneralPaperStoredPreparedRead.budget_source model S A start installed prepared hRead hRoot).1
  have hBudgetWork := GeneralPaperStoredPreparedReadWork.budget_work model S A layoutStart start plan full installed ctx prepared hRead hHeaders hRoot
  have hBudgetWidth := rationalWordWidth_of_height hB
  obtain ⟨fieldStart,hLoad,_,hChildRead,hChildHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 64 installed
    (GeneralPaperPreparedRecordCursor.schema model S A prepared) (GeneralPaperPreparedRecordCursor.child model S A prepared)
    GeneralPaperPreparedRecordCursor.fields hRead hRoot ⟨1,by decide⟩
  let child := GeneralPaperPreparedRecordCursor.child model S A prepared .segments fieldStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  have childCtx := GeneralPaperStoredReadContext.atRoot ctx child.root.reference
  have headers := fun header hh => hHeaders header (hChildHeaders header hh)
  have hLeft := GeneralPaperStoredEndpointWork.bounds model S A layoutStart fieldStart plan full loaded childCtx prepared.segments hChildRead headers rfl .left index
  have hRight := GeneralPaperStoredEndpointWork.bounds model S A layoutStart fieldStart plan full loaded childCtx prepared.segments hChildRead headers rfl .right index
  have hComp := GeneralPaperPositiveSegmentCompaction.compact_height l h
  have hP : ∀ g,RationalHeight ((prepared.segments.left.read index).read g) s := by
    intro g
    rw [prepared.segments.left_correct]
    exact (hComp.2 index g).1
  have hQ : ∀ g,RationalHeight ((prepared.segments.right.read index).read g) s := by
    intro g
    rw [prepared.segments.right_correct]
    exact (hComp.2 index g).2
  have hLeftBound := GeneralPaperStoredEndpointWork.height_bound model A s (prepared.segments.left.read index) hP
  have hRightBound := GeneralPaperStoredEndpointWork.height_bound model A s (prepared.segments.right.read index) hQ
  simp only [GeneralPaperStoredEndpointRows.matrix] at hLeft hRight
  have hS : s ≤ GeneralPaperEqualBitGroups.base s b prepared.midpointBits := (le_max_left _ _).trans (le_max_right _ _)
  have hT : prepared.midpointBits + 2 ≤ GeneralPaperEqualBitGroups.base s b prepared.midpointBits := (le_max_right _ _).trans (le_max_right _ _)
  have ht : RationalHeight (GeneralPaperEqualPreparedCache.midpoint prepared fresh) (GeneralPaperEqualBitGroups.base s b prepared.midpointBits) := by
    rw [GeneralPaperEqualPreparedCache.midpoint_eq]
    exact (dyadicMidpointSample_height _ _).mono hT
  have hArray := GeneralPaperStoredInterpolationWork.array_rows_work model A (GeneralPaperEqualBitGroups.base s b prepared.midpointBits)
    prepared.budget (GeneralPaperEqualPreparedCache.midpoint prepared fresh) (prepared.segments.left.read index) (prepared.segments.right.read index)
    ctx.positive (binaryWordWidth_le_of_lt_pow ctx.positive hLeft.1) (hs.trans hS) (hB.mono (le_max_left _ _)) ht
    (fun g => (hP g).mono hS) (fun g => (hQ g).mono hS)
  have hLoadWork := GeneralPaperStoredRecordReadWork.work model S A layoutStart start 64 plan full installed ctx
    (GeneralPaperPreparedRecordCursor.schema model S A prepared) (GeneralPaperPreparedRecordCursor.child model S A prepared)
    GeneralPaperPreparedRecordCursor.fields hRead hHeaders hRoot ⟨1,by decide⟩
  obtain ⟨_,hLeftValues,_,_⟩ := GeneralPaperStoredEndpointRows.source model S A fieldStart loaded full childCtx.contract prepared.segments hChildRead headers rfl .left index
  obtain ⟨_,hRightValues,_,_⟩ := GeneralPaperStoredEndpointRows.source model S A fieldStart loaded full childCtx.contract prepared.segments hChildRead headers rfl .right index
  simp only [GeneralPaperStoredEndpointRows.matrix] at hLeftValues hRightValues
  change (GeneralPaperStoredChildRead.load model A installed 0 1).1 = some (⟨A,loaded⟩ : GeneralPaperStoredChildRead.Child) at hLoad
  change (GeneralPaperStoredChildRead.load model A installed 0 1).2 ≤ _ at hLoadWork
  simp only [GeneralPaperStoredPreparedGroups.run,hBudget,hLoad,hLeftValues,hRightValues]
  unfold bound
  have hL := hLeft.2.trans hLeftBound
  have hR := hRight.2.trans hRightBound
  omega

end Blotto.GeneralPaperStoredPreparedGroupsWork
