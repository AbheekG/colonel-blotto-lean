import Blotto.GeneralPaperDirectoryExtensionLifetime

/-! Complete actual outer attachment: both pointer encoders, copied
field records, extension and every parent partial/full price coexist with
resident memory. Incoming inner memory is extended in place in the paper
RAM model; its resident ownership is counted separately and additively. -/
namespace Blotto.GeneralPaperOuterAttachmentLifetime
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualOuterFieldLayout (Fields canonical)
open GeneralPaperUnifiedFieldValue (encode)
open GeneralPaperPayloadMemoryOwnership (Bounded cellSize)
open GeneralPaperEncodedScalarStorage
open GeneralPaperPayloadInstallationLifetime (cap)
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit unit_bounds)
open GeneralPaperRulerCursorLifetime (encoding)
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def directory (model : RationalCostModel) (S I A : ℕ) (fields : Fields A) (inner : Installed I) (tag : ℕ) :
    GeneralPaperFieldDirectory.Directory A :=
  GeneralPaperStoredOuterDirectory.directory A fields (GeneralPaperStoredWordEncoding.word model S A inner.root.value).1
    (GeneralPaperStoredWordEncoding.word model S A tag).1

def controls (model : RationalCostModel) (S I A prefixWork : ℕ) (fields : Fields A) (inner : Installed I) (tag : ℕ) : List ℕ :=
  let branch := GeneralPaperStoredWordEncoding.word model S A inner.root.value
  let marker := GeneralPaperStoredWordEncoding.word model S A tag
  let actual := GeneralPaperStoredDirectoryExtension.install model S A (directory model S I A fields inner tag) inner.memory
  [S,I,A,prefixWork,inner.work,branch.2,marker.2,prefixWork + inner.work,
    prefixWork + inner.work + branch.2,prefixWork + inner.work + branch.2 + marker.2,actual.work,
    prefixWork + inner.work + branch.2 + marker.2 + actual.work,
    (GeneralPaperStoredOuterAttachment.finish model S I A prefixWork fields inner tag).work]

def extraWindow (model : RationalCostModel) (S I A prefixWork : ℕ) (fields : Fields A) (inner : Installed I) (tag : ℕ) : ℕ :=
  GeneralPaperWordEncodingLifetime.window model S A inner.root.value + GeneralPaperWordEncodingLifetime.window model S A tag +
    GeneralPaperOuterFieldCursorLifetime.fieldsFoot S fields + I + natBits inner.root.value + natBits tag +
    GeneralPaperEncodedScalarStorage.fields S (controls model S I A prefixWork fields inner tag) + 256 * S

def extraProfile (model : RationalCostModel) (S A P : ℕ) : ℕ := 2 * encoding model S A + unit model S A P

theorem extra_window_bound (model : RationalCostModel) (S I A start prefixWork tag P : ℕ) (inner : Installed I)
    (hA : 0 < A) (hI : I ≤ A) (hTag : tag < 2 ^ A)
    (hCap : start + (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A)
    (hWork : (GeneralPaperStoredOuterAttachment.finish model S I A prefixWork (canonical A start) inner tag).work ≤ P) :
    extraWindow model S I A prefixWork (canonical A start) inner tag ≤ extraProfile model S A P := by
  have hRootWidth := GeneralPaperStoredReferenceReadWork.fixed_word_width inner.root
  have hTagWidth := binaryWordWidth_le_of_lt_pow hA hTag
  have hBranch := GeneralPaperWordEncodingLifetime.word_bound model S A inner.root.value (A + 8) (by omega)
  have hMarker := GeneralPaperWordEncodingLifetime.word_bound model S A tag (A + 8) (by omega)
  change GeneralPaperWordEncodingLifetime.window model S A inner.root.value ≤ encoding model S A at hBranch
  change GeneralPaperWordEncodingLifetime.window model S A tag ≤ encoding model S A at hMarker
  have hRootBits : natBits inner.root.value ≤ A + 2 := by unfold natBits; omega
  have hTagBits : natBits tag ≤ A + 1 := by unfold natBits; omega
  have hWhole := hWork
  change prefixWork + inner.work + (GeneralPaperStoredWordEncoding.word model S A inner.root.value).2 +
    (GeneralPaperStoredWordEncoding.word model S A tag).2 +
    (GeneralPaperStoredDirectoryExtension.install model S A (directory model S I A (canonical A start) inner tag) inner.memory).work +
    128 * (S + I + A + 1) ≤ P at hWork
  have hFields := fields_bound S (natBits (cap S A P)) (controls model S I A prefixWork (canonical A start) inner tag) (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change GeneralPaperEncodedScalarStorage.fields S _ ≤ 13 * (natBits (cap S A P) + S) + 32 * S at hFields
  have hRange := GeneralPaperMeasuredBlockLayout.range model S A start (GeneralPaperEqualMeasuredSelectedPlan.header model S A)
  rw [GeneralPaperEqualOuterFieldLayout.regions] at hRange
  have hOwner : ∀ r ∈ [(canonical A start).control,(canonical A start).value,(canonical A start).record],
      GeneralPaperMeasuredLayoutStorage.regionFoot S r ≤ GeneralPaperMeasuredLayoutStorage.regionBound S A :=
    fun r hr => GeneralPaperMeasuredLayoutStorage.region_bound S A r hA ((hRange r hr).2.trans_lt hCap)
  have hControl := hOwner (canonical A start).control (List.mem_cons_self ..)
  have hValue := hOwner (canonical A start).value (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hRecord := hOwner (canonical A start).record (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hUnit := unit_bounds model S A P
  have hParent : GeneralPaperOuterFieldCursorLifetime.fieldsFoot S (canonical A start) + I + natBits inner.root.value + natBits tag +
      GeneralPaperEncodedScalarStorage.fields S (controls model S I A prefixWork (canonical A start) inner tag) + 256 * S ≤ unit model S A P := by
    unfold GeneralPaperOuterFieldCursorLifetime.fieldsFoot
    unfold GeneralPaperMeasuredLayoutStorage.regionBound at hControl hValue hRecord
    omega
  unfold extraWindow extraProfile
  omega

def window (model : RationalCostModel) (S I A prefixWork : ℕ) (fields : Fields A) (inner : Installed I) (tag : ℕ) : ℕ :=
  GeneralPaperDirectoryExtensionLifetime.window model S A (directory model S I A fields inner tag) inner.memory +
    extraWindow model S I A prefixWork fields inner tag

def profile (model : RationalCostModel) (S A B P : ℕ) : ℕ :=
  GeneralPaperDirectoryExtensionLifetime.profile model S A B + extraProfile model S A P

theorem window_bound (model : RationalCostModel) (S I A start prefixWork tag P : ℕ) (inner : Installed I)
    (hA : 0 < A) (hI : I ≤ A) (hTag : tag < 2 ^ A)
    (hCap : start + (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A)
    (hWork : (GeneralPaperStoredOuterAttachment.finish model S I A prefixWork (canonical A start) inner tag).work ≤ P) :
    window model S I A prefixWork (canonical A start) inner tag ≤
      profile model S A (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum P :=
  Nat.add_le_add (GeneralPaperDirectoryExtensionLifetime.window_bound model S A start _ _ inner.memory
    (GeneralPaperStoredOuterDirectory.safe model S A start _ _) (GeneralPaperStoredOuterDirectory.covered model S A start _ _)
    (GeneralPaperStoredOuterDirectory.positive model S A hA) hA hCap)
    (extra_window_bound model S I A start prefixWork tag P inner hA hI hTag hCap hWork)

theorem resident_coexistence (model : RationalCostModel) (S I A start prefixWork tag P B : ℕ) (inner : Installed I)
    (hMemory : Bounded encode inner.memory B) (hA : 0 < A) (hI : I ≤ A) (hTag : tag < 2 ^ A)
    (hCap : start + (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A)
    (hWork : (GeneralPaperStoredOuterAttachment.finish model S I A prefixWork (canonical A start) inner tag).work ≤ P) :
    let output := GeneralPaperStoredOuterAttachment.finish model S I A prefixWork (canonical A start) inner tag
    ∃ keys : Finset ℕ,(∀ key,output.memory key ≠ none → key ∈ keys) ∧
      (∑ key ∈ keys,cellSize encode output.memory key) + window model S I A prefixWork (canonical A start) inner tag ≤
        B + (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum +
          profile model S A (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum P := by
  obtain ⟨keys,hSupport,hInstall⟩ := GeneralPaperDirectoryExtensionLifetime.resident_coexistence model S A start B
    (GeneralPaperEqualMeasuredSelectedPlan.header model S A) (directory model S I A (canonical A start) inner tag) inner.memory hMemory
    (GeneralPaperStoredOuterDirectory.safe model S A start _ _) (GeneralPaperStoredOuterDirectory.covered model S A start _ _)
    (GeneralPaperStoredOuterDirectory.positive model S A hA) hA hCap
  have hExtra := extra_window_bound model S I A start prefixWork tag P inner hA hI hTag hCap hWork
  have hMemoryEq : (GeneralPaperStoredOuterAttachment.finish model S I A prefixWork (canonical A start) inner tag).memory =
      (GeneralPaperStoredDirectoryExtension.install model S A (directory model S I A (canonical A start) inner tag) inner.memory).memory := rfl
  refine ⟨keys,hSupport,?_⟩
  rw [hMemoryEq]
  dsimp only [window,profile]
  omega

theorem profile_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A B P r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x)
    (hS : Tight S L) (hA : Tight A L) (hB : Bound B r L) (hP : Small P L) (hrSmall : Small r L) :
    Bound (fun x => profile model (S x) (A x) (B x) (P x)) r L := by
  have hExtension := GeneralPaperDirectoryExtensionLifetime.profile_rate model hFast S A B r L hL hr hS hA hB hrSmall
  have hEncoding := GeneralPaperHeaderCountLifetimeRates.encoding_rate model hFast S A L hL hS hA
  have hUnit := GeneralPaperMeasuredPlanLifetimeRates.unit_rate model hFast S A P L hL hS hA hP
  have hExtra : Polylog (fun x => extraProfile model (S x) (A x) (P x)) L := by
    unfold extraProfile encoding
    fun_prop
  exact bound_add _ _ r L hL hExtension (rate_mono hExtra hr)

end Blotto.GeneralPaperOuterAttachmentLifetime
