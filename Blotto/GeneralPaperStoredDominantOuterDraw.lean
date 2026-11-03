import Blotto.GeneralPaperStoredDominantEmission

/-! Dominant outer dispatch reads its actual stored address, zero marker and
root, then copies the counted row from that same memory. It consumes no bits. -/
namespace Blotto.GeneralPaperStoredDominantOuterDraw
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperStoredChildRead (Child)
open GeneralPaperMixedReferenceMemory (Word)
open GeneralPaperEqualOuterFieldLayout
open GeneralPaperHeaderCountInstallation (Contract)
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192

def load (model : RationalCostModel) (A : ℕ) (outer : Installed A) : Option Child × ℕ :=
  let address := GeneralPaperStoredOuterRead.address model A outer
  let marker := GeneralPaperStoredOuterRead.field model A outer 2
  match address.1,marker.1 with
  | some width,some ⟨B,tag⟩ =>
    if tag.value = 0 then
      let pointer := GeneralPaperStoredOuterRead.field model A outer 0
      match pointer.1 with
      | none => (none,address.2 + marker.2 + pointer.2 + B + 128 * (A + 1))
      | some ⟨C,root⟩ =>
        let actual := GeneralPaperStoredWordEncoding.word model A width root.value
        (some ⟨width,GeneralPaperStoredScalarRead.atRoot outer actual.1⟩,
          address.2 + marker.2 + pointer.2 + actual.2 + B + C + 128 * (A + B + C + width + 1))
    else (none,address.2 + marker.2 + B + 128 * (A + 1))
  | _,_ => (none,address.2 + marker.2 + 64 * (A + 1))

def run (model : RationalCostModel) (A : ℕ) (outer : Installed A) : GeneralPaperStoredRouteEmission.Result :=
  let child := load model A outer
  match child.1 with
  | none => ⟨none,0,child.2 + 64 * (A + 1)⟩
  | some ⟨B,inner⟩ =>
    let actual := GeneralPaperStoredDominantEmission.run model B inner
    ⟨actual.values,actual.count,child.2 + actual.work + 64 * (A + B + 1)⟩

theorem load_source (model : RationalCostModel) (A : ℕ) (outer : Installed A) (root : FixedBinaryWord A)
    (hAddress : (GeneralPaperStoredOuterRead.address model A outer).1 = some A)
    (hMarker : (GeneralPaperStoredOuterRead.field model A outer 2).1 = some (⟨A,FixedBinaryWord.ofNat A 0⟩ : Word))
    (hRoot : (GeneralPaperStoredOuterRead.field model A outer 0).1 = some (⟨A,FixedBinaryWord.ofNat A root.value⟩ : Word)) :
    (load model A outer).1 = some (⟨A,GeneralPaperStoredScalarRead.atRoot outer root⟩ : Child) := by
  simp only [load,hAddress,hMarker,FixedBinaryWord.value_ofNat A 0 (Nat.two_pow_pos A),ite_true,hRoot,
    GeneralPaperStoredWordEncoding.word_data,GeneralPaperStoredGroupedLoad.reencode]

theorem attached_load (model : RationalCostModel) (S A start prefixWork : ℕ) (inner : Installed A)
    (hA : 0 < A) (hCap : start + (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A) :
    let outer := GeneralPaperStoredOuterAttachment.finish model S A A prefixWork (canonical A start) inner 0
    (load model A outer).1 = some (⟨A,GeneralPaperStoredScalarRead.atRoot outer inner.root⟩ : Child) := by
  dsimp only
  let outer := GeneralPaperStoredOuterAttachment.finish model S A A prefixWork (canonical A start) inner 0
  have hRead := GeneralPaperStoredOuterAttachment.outer_readback model S A A start prefixWork inner 0 hA hCap
  have hAddress := GeneralPaperStoredOuterAttachment.address_source model S A A start prefixWork inner 0 hA hCap
  have hBranch := GeneralPaperStoredOuterRead.field_source model A outer (canonical A start) _ _ hRead rfl ⟨0,by decide⟩
  have hMarker := GeneralPaperStoredOuterRead.field_source model A outer (canonical A start) _ _ hRead rfl ⟨2,by decide⟩
  exact load_source model A outer inner.root hAddress hMarker hBranch

theorem attached_source {n : ℕ} (model : RationalCostModel) (S A prefixWork chosen : ℕ)
    (row : RationalResourceArray n) (inner : Installed A)
    (hContract : Contract model A inner (GeneralPaperStoredDominantCursor.expected model S A chosen row 0))
    (hRoot : inner.root = (GeneralPaperStoredDominantCursor.expected model S A chosen row 0).root.reference)
    (hA : 0 < A) (hInnerCap : (GeneralPaperStoredDominantCursor.plan model S A chosen row).sizes.sum < 2 ^ A)
    (hOuterCap : (GeneralPaperStoredDominantCursor.plan model S A chosen row).sizes.sum +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A) :
    let outer := GeneralPaperStoredOuterAttachment.finish model S A A prefixWork
      (canonical A (GeneralPaperStoredDominantCursor.plan model S A chosen row).sizes.sum) inner 0
    (run model A outer).values = some row.data ∧ (run model A outer).count = n := by
  dsimp only
  let plan := GeneralPaperStoredDominantCursor.plan model S A chosen row
  let outer := GeneralPaperStoredOuterAttachment.finish model S A A prefixWork (canonical A plan.sizes.sum) inner 0
  let loaded := GeneralPaperStoredScalarRead.atRoot outer inner.root
  have hSafe := (GeneralPaperStoredDominantCursor.success model S A 0 chosen row []).2.2.1
  have hNew := GeneralPaperStoredOuterAttachment.inner_contract model S A A prefixWork plan _ inner 0 hSafe hA hInnerCap hContract hA hOuterCap
  have hLoaded : Contract model A loaded (GeneralPaperStoredDominantCursor.expected model S A chosen row 0) := hNew
  have hLoad := attached_load model S A plan.sizes.sum prefixWork inner hA hOuterCap
  obtain ⟨_,hValue,hCount,_⟩ := GeneralPaperStoredDominantEmission.source model S A 0 chosen loaded row hLoaded hRoot
  dsimp only [outer,loaded,plan] at hLoad hValue hCount
  simpa only [run,hLoad] using And.intro hValue hCount

end Blotto.GeneralPaperStoredDominantOuterDraw
