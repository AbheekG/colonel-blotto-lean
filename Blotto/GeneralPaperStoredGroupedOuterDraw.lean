import Blotto.GeneralPaperStoredGroupedLoad

/-! Mixed-width grouped draw first loads/narrows the actual outer pointer,
then runs the verified complete inner draw on the same extended memory. -/
namespace Blotto.GeneralPaperStoredGroupedOuterDraw
open GeneralPaperFieldDirectory GeneralPaperEqualOuterFieldLayout
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperStoredChildRead (Child)
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

def run {S : Type*} (model : RationalCostModel) (A : ℕ) (outer : Installed A) (cap : ℕ) (tape : ℕ → List Bool)
    (next : S → Bool × S) (state : S) : GeneralPaperEqualBooleanTrial.Result (Array ℚ) S :=
  let child := GeneralPaperStoredGroupedLoad.load model A outer
  match child.1 with
  | none => ⟨none,state,0,child.2 + 64 * (A + 1)⟩
  | some ⟨B,inner⟩ =>
    let actual := GeneralPaperStoredAllocationDraw.run model B inner cap tape next state
    ⟨actual.output,actual.state,actual.reads,child.2 + actual.work + 64 * (A + B + 1)⟩

def Refines (model : RationalCostModel) (A : ℕ) (outer : Installed A)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l) : Prop :=
  ∀ cap tape fresh,
    (run model A outer cap (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape)
      GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).output =
        (GeneralPaperEqualFullBitDraw.run sampler.categorical model sampler.address cap tape fresh).output.map RationalResourceArray.data ∧
    (run model A outer cap (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape)
      GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).reads =
        (GeneralPaperEqualFullBitDraw.run sampler.categorical model sampler.address cap tape fresh).reads

theorem attached_load (model : RationalCostModel) (S I start prefixWork : ℕ) (inner : Installed I)
    (hCap : start + (GeneralPaperEqualMeasuredSelectedPlan.header model S (I + 1)).sizes.sum < 2 ^ (I + 1)) :
    let outer := GeneralPaperStoredOuterAttachment.finish model S I (I + 1) prefixWork (canonical (I + 1) start) inner 1
    (GeneralPaperStoredGroupedLoad.load model (I + 1) outer).1 =
      some (⟨I,GeneralPaperStoredScalarRead.atRoot outer inner.root⟩ : Child) := by
  dsimp only
  let outer := GeneralPaperStoredOuterAttachment.finish model S I (I + 1) prefixWork (canonical (I + 1) start) inner 1
  have hRead := GeneralPaperStoredOuterAttachment.outer_readback model S I (I + 1) start prefixWork inner 1 (by omega) hCap
  have hAddress := GeneralPaperStoredOuterAttachment.address_source model S I (I + 1) start prefixWork inner 1 (by omega) hCap
  have hBranch := GeneralPaperStoredOuterRead.field_source model (I + 1) outer (canonical (I + 1) start) _ _ hRead rfl ⟨0,by decide⟩
  have hMarker := GeneralPaperStoredOuterRead.field_source model (I + 1) outer (canonical (I + 1) start) _ _ hRead rfl ⟨2,by decide⟩
  exact GeneralPaperStoredGroupedLoad.source model I outer inner.root hAddress hMarker hBranch

theorem attached_source (model : RationalCostModel) (S prefixWork : ℕ) (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (inner : Installed sampler.address)
    (hContract : Contract model sampler.address inner (GeneralPaperSamplerRecordCursor.expected model S sampler.address sampler 0))
    (hRoot : inner.root = (GeneralPaperSamplerRecordCursor.expected model S sampler.address sampler 0).root.reference)
    (hInnerCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum < 2 ^ sampler.address)
    (hOuterCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S (sampler.address + 1)).sizes.sum < 2 ^ (sampler.address + 1)) :
    let outer := GeneralPaperStoredOuterAttachment.finish model S sampler.address (sampler.address + 1) prefixWork
      (canonical (sampler.address + 1) (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum) inner 1
    ∀ cap tape fresh,
      (run model (sampler.address + 1) outer cap (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape)
        GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).output =
          (GeneralPaperEqualFullBitDraw.run sampler.categorical model sampler.address cap tape fresh).output.map RationalResourceArray.data ∧
      (run model (sampler.address + 1) outer cap (GeneralPaperStoredBooleanRejection.blocks sampler.prepared tape)
        GeneralPaperBooleanFreshWord.nextList (List.ofFn fresh)).reads =
          (GeneralPaperEqualFullBitDraw.run sampler.categorical model sampler.address cap tape fresh).reads := by
  dsimp only
  let plan := GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler
  let outer := GeneralPaperStoredOuterAttachment.finish model S sampler.address (sampler.address + 1) prefixWork
    (canonical (sampler.address + 1) plan.sizes.sum) inner 1
  let loaded := GeneralPaperStoredScalarRead.atRoot outer inner.root
  have hI := GeneralPaperStoredNativeConstruction.address_positive sampler
  have hSafe := (GeneralPaperSamplerRecordCursor.success model S sampler.address 0 sampler []).2.2.1
  have hNew := GeneralPaperStoredOuterAttachment.inner_contract model S sampler.address (sampler.address + 1) prefixWork plan _ inner 1
    hSafe hI hInnerCap hContract (by omega) hOuterCap
  have hLoaded : Contract model sampler.address loaded (GeneralPaperSamplerRecordCursor.expected model S sampler.address sampler 0) := hNew
  have hLoad := attached_load model S sampler.address plan.sizes.sum prefixWork inner hOuterCap
  intro cap tape fresh
  have hSource := GeneralPaperStoredAllocationDraw.source model S sampler.address 0 loaded sampler hLoaded hRoot hI
    (by simpa only [Nat.zero_add] using hInnerCap) cap tape fresh
  dsimp only [outer,loaded,plan] at hLoad hSource
  simpa only [run,hLoad] using hSource

end Blotto.GeneralPaperStoredGroupedOuterDraw
