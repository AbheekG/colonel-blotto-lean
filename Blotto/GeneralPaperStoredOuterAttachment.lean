import Blotto.GeneralPaperStoredOuterRead

/-! Install the outer fields into the actual returned inner memory. No inner
reinstallation or independent bank is introduced. The prior inner contract
is preserved by the actual outer owner boundary. -/
namespace Blotto.GeneralPaperStoredOuterAttachment
open GeneralPaperFieldDirectory GeneralPaperEqualOuterFieldLayout
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperSamplerRecordInstallation (Readback)
open GeneralPaperStoredDirectoryPreservation (Below)
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192

def finish (model : RationalCostModel) (S I A prefixWork : ℕ) (fields : Fields A) (inner : Installed I) (tag : ℕ) : Installed A :=
  let branch := GeneralPaperStoredWordEncoding.word model S A inner.root.value
  let marker := GeneralPaperStoredWordEncoding.word model S A tag
  let directory := GeneralPaperStoredOuterDirectory.directory A fields branch.1 marker.1
  let actual := GeneralPaperStoredDirectoryExtension.install model S A directory inner.memory
  ⟨actual.memory,actual.root,prefixWork + inner.work + branch.2 + marker.2 + actual.work + 128 * (S + I + A + 1)⟩

def innerView {I A : ℕ} (outer : Installed A) (inner : Installed I) : Installed I := ⟨outer.memory,inner.root,inner.work⟩

theorem root (model : RationalCostModel) (S I A prefixWork : ℕ) (fields : Fields A) (inner : Installed I) (tag : ℕ) :
    (finish model S I A prefixWork fields inner tag).root = fields.record.reference := rfl

theorem outer_readback (model : RationalCostModel) (S I A start prefixWork : ℕ) (inner : Installed I) (tag : ℕ)
    (hA : 0 < A) (hCap : start + (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A) :
    Readback model A (finish model S I A prefixWork (canonical A start) inner tag)
      (GeneralPaperStoredOuterDirectory.directory A (canonical A start) (FixedBinaryWord.ofNat A inner.root.value) (FixedBinaryWord.ofNat A tag)) := by
  have h := GeneralPaperStoredDirectoryExtension.readback model S A start (GeneralPaperEqualMeasuredSelectedPlan.header model S A)
    (GeneralPaperStoredOuterDirectory.directory A (canonical A start) (FixedBinaryWord.ofNat A inner.root.value) (FixedBinaryWord.ofNat A tag)) inner.memory
    (GeneralPaperStoredOuterDirectory.safe model S A start _ _) (GeneralPaperStoredOuterDirectory.covered model S A start _ _)
    (GeneralPaperStoredOuterDirectory.positive model S A hA) hA hCap
  dsimp only [Readback] at h ⊢
  simpa only [finish,GeneralPaperStoredWordEncoding.word_data] using h

theorem memory_before_outer (model : RationalCostModel) (S I A start prefixWork : ℕ) (inner : Installed I) (tag : ℕ)
    (hA : 0 < A) (hCap : start + (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A) :
    Below start (finish model S I A prefixWork (canonical A start) inner tag).memory inner.memory := by
  have h := GeneralPaperStoredDirectoryPreservation.writes_after model S A start (GeneralPaperEqualMeasuredSelectedPlan.header model S A)
    (GeneralPaperStoredOuterDirectory.directory A (canonical A start) (FixedBinaryWord.ofNat A inner.root.value) (FixedBinaryWord.ofNat A tag)) inner.memory
    (GeneralPaperStoredOuterDirectory.safe model S A start _ _) hA hCap
  simpa only [finish,GeneralPaperStoredWordEncoding.word_data] using h

theorem inner_contract (model : RationalCostModel) (S I A prefixWork : ℕ) (plan : GeneralPaperMeasuredBlockPlan.Plan)
    (directory : Directory I) (inner : Installed I) (tag : ℕ)
    (hSafe : GeneralPaperFieldDirectorySafety.Safe (GeneralPaperMeasuredBlockLayout.run model S I 0 plan).1 directory)
    (hI : 0 < I) (hInnerCap : plan.sizes.sum < 2 ^ I) (hContract : Contract model I inner directory)
    (hA : 0 < A) (hOuterCap : plan.sizes.sum + (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A) :
    Contract model I (innerView (finish model S I A prefixWork (canonical A plan.sizes.sum) inner tag) inner) directory := by
  have hAgree := memory_before_outer model S I A plan.sizes.sum prefixWork inner tag hA hOuterCap
  exact GeneralPaperStoredReadbackPreservation.contract model S I 0 plan directory inner _ hSafe hI
    (by simpa only [Nat.zero_add] using hInnerCap) hContract (by simpa only [Nat.zero_add,innerView] using hAgree)

theorem address_source (model : RationalCostModel) (S I A start prefixWork : ℕ) (inner : Installed I) (tag : ℕ)
    (hA : 0 < A) (hCap : start + (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A) :
    (GeneralPaperStoredOuterRead.address model A (finish model S I A prefixWork (canonical A start) inner tag)).1 = some A :=
  (GeneralPaperStoredOuterRead.address_source model A _ (canonical A start) _ _
    (outer_readback model S I A start prefixWork inner tag hA hCap) rfl).1

end Blotto.GeneralPaperStoredOuterAttachment
