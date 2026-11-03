import Blotto.GeneralPaperStoredRouteEmissionWork
import Blotto.GeneralPaperStoredSamplerEmission

/-! Full route emission is charged at prepared and sampler roots, with each
actual child access paid exactly once in the same enclosing memory. -/
namespace Blotto.GeneralPaperStoredEmissionWork
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperStoredReadContext (Context)
open GeneralPaperStoredChildRead (Child)
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

def preparedBound (model : RationalCostModel) (A n m s : ℕ) : ℕ :=
  GeneralPaperStoredRouteEmissionWork.bound model A n m s +
    GeneralPaperStoredReferenceReadWork.readBound model A A + 256 * (A + 1)

def samplerBound (model : RationalCostModel) (A n m s : ℕ) : ℕ :=
  preparedBound model A n m s + GeneralPaperStoredReferenceReadWork.readBound model A A + 256 * (A + 1)

theorem prepared_work (model : RationalCostModel) (S A layoutStart start s : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (full : Directory A) (installed : Installed A) (ctx : Context model S A layoutStart plan full installed)
    (prepared : GeneralPaperEqualPreparedCache.Prepared G l)
    (hRead : Readback model A installed (GeneralPaperPreparedRecordCursor.expected model S A prepared start))
    (hHeaders : ∀ header ∈ (GeneralPaperPreparedRecordCursor.expected model S A prepared start).headers,header ∈ full.headers)
    (hRoot : installed.root = (GeneralPaperPreparedRecordCursor.expected model S A prepared start).root.reference)
    (groups : FixedArrayTable m ℚ) (hs : 2 ≤ s) (hC : ∀ j,RationalHeight (prepared.routes.table.read j).2 s)
    (hG : ∀ g,RationalHeight (groups.read g) s) :
    (GeneralPaperStoredPreparedEmission.run model A installed groups.data).work ≤ preparedBound model A n m s := by
  obtain ⟨fieldStart,hLoad,_,hChildRead,hChildHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 64 installed
    (GeneralPaperPreparedRecordCursor.schema model S A prepared) (GeneralPaperPreparedRecordCursor.child model S A prepared)
    GeneralPaperPreparedRecordCursor.fields hRead hRoot ⟨0,by decide⟩
  let child := GeneralPaperPreparedRecordCursor.child model S A prepared .routes fieldStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  have hEmit := GeneralPaperStoredRouteEmissionWork.work model S A layoutStart fieldStart s plan full loaded
    (GeneralPaperStoredReadContext.atRoot ctx child.root.reference) prepared.routes.table hChildRead
    (fun header hh => hHeaders header (hChildHeaders header hh)) rfl groups hs hC hG
  have hLoadWork := GeneralPaperStoredRecordReadWork.work model S A layoutStart start 64 plan full installed ctx
    (GeneralPaperPreparedRecordCursor.schema model S A prepared) (GeneralPaperPreparedRecordCursor.child model S A prepared)
    GeneralPaperPreparedRecordCursor.fields hRead hHeaders hRoot ⟨0,by decide⟩
  change (GeneralPaperStoredChildRead.load model A installed 0 0).1 = some (⟨A,loaded⟩ : Child) at hLoad
  change (GeneralPaperStoredChildRead.load model A installed 0 0).2 ≤ _ at hLoadWork
  rw [(GeneralPaperStoredPreparedEmission.trace model A installed loaded groups.data hLoad).2.2]
  unfold preparedBound
  omega

theorem sampler_work (model : RationalCostModel) (S A start s : ℕ) (installed : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (ctx : Context model S A start (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A sampler)
      (GeneralPaperSamplerRecordCursor.expected model S A sampler start) installed)
    (hRoot : installed.root = (GeneralPaperSamplerRecordCursor.expected model S A sampler start).root.reference)
    (groups : FixedArrayTable m ℚ) (hs : 2 ≤ s) (hC : ∀ j,RationalHeight (sampler.prepared.routes.table.read j).2 s)
    (hG : ∀ g,RationalHeight (groups.read g) s) :
    (GeneralPaperStoredSamplerEmission.run model A installed groups.data).work ≤ samplerBound model A n m s := by
  obtain ⟨fieldStart,hLoad,_,hRead,hHeaders,_⟩ := GeneralPaperStoredChildRead.record_child model A start 64 installed
    (GeneralPaperSamplerRecordCursor.schema model S A sampler) (GeneralPaperSamplerRecordCursor.child model S A sampler)
    GeneralPaperSamplerRecordCursor.fields ctx.contract.2.1 hRoot ⟨0,by decide⟩
  let child := GeneralPaperSamplerRecordCursor.child model S A sampler .prepared fieldStart
  let loaded := GeneralPaperStoredScalarRead.atRoot installed child.root.reference
  have hEmit := prepared_work model S A start fieldStart s _ _ loaded
    (GeneralPaperStoredReadContext.atRoot ctx child.root.reference) sampler.prepared hRead hHeaders rfl groups hs hC hG
  have hLoadWork := GeneralPaperStoredRecordReadWork.work model S A start start 64 _ _ installed ctx
    (GeneralPaperSamplerRecordCursor.schema model S A sampler) (GeneralPaperSamplerRecordCursor.child model S A sampler)
    GeneralPaperSamplerRecordCursor.fields ctx.contract.2.1 (fun _ hh => hh) hRoot ⟨0,by decide⟩
  change (GeneralPaperStoredChildRead.load model A installed 0 0).1 = some (⟨A,loaded⟩ : Child) at hLoad
  change (GeneralPaperStoredChildRead.load model A installed 0 0).2 ≤ _ at hLoadWork
  rw [(GeneralPaperStoredSamplerEmission.trace model A installed loaded groups.data hLoad).2.2]
  unfold samplerBound
  omega

end Blotto.GeneralPaperStoredEmissionWork
