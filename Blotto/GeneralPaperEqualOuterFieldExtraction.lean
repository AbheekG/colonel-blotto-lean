import Blotto.GeneralPaperEqualOuterFieldProgram

/-! The selected native source computes its measured layout, selects the
actual inner record root, extracts the actual outer fields and installs them.
No header list, region, size or capacity oracle is an execution input. The
only original budget remains inside the unchanged inner branch description. -/
namespace Blotto.GeneralPaperEqualOuterFieldExtraction
open GeneralPaperEqualMeasuredLayout GeneralPaperEqualSelectedSampler GeneralPaperEqualOuterFieldLayout
open GeneralPaperSequentialLayout
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def branchTag {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) : ℕ := match a.branch with | .dominant _ _ _ _ => 0 | .grouped _ _ _ _ => 1

def finish (model : RationalCostModel) (S I A baseWork : ℕ) (fields : Fields A) (innerRoot : Region I) (tag : ℕ) :
    GeneralPaperEqualOuterFieldProgram.Installed A × ℕ :=
  let branch := GeneralPaperStoredWordEncoding.word model S A innerRoot.reference.value
  let marker := GeneralPaperStoredWordEncoding.word model S A tag
  let installed := GeneralPaperEqualOuterFieldProgram.install model S A fields branch.1 marker.1
  let total := baseWork + branch.2 + marker.2 + installed.work + 128 * (S + I + A + 1)
  (⟨installed.references,installed.naturals,installed.root,total⟩,total)

def run {n : ℕ} (model : RationalCostModel) (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) : Option (GeneralPaperEqualOuterFieldProgram.Installed a.address) × ℕ :=
  let layout := GeneralPaperEqualMeasuredLayout.run model S a
  let selected := GeneralPaperLastRegionSelection.run S (innerWidth a) layout.inner
  let fields := extract S a.address layout.outer
  let baseWork := layout.work + selected.2 + fields.2
  match selected.1,fields.1 with
  | some root,some fields =>
    let actual := finish model S (innerWidth a) a.address baseWork fields root (branchTag a)
    (some actual.1,actual.2)
  | _,_ => (none,baseWork + 128 * (S + innerWidth a + a.address + 1))

theorem inner_positive {n : ℕ} (model : RationalCostModel) (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) : 0 < (inner model S a).sizes.sum := by
  have hA : 0 < a.address := (widths_positive a).2
  dsimp only [GeneralPaperEqualMeasuredLayout.inner]
  rw [GeneralPaperEqualMeasuredSelectedPlan.branch_sum]
  cases hBranch : a.branch with
  | dominant chosen heavy source correct =>
    dsimp only [GeneralPaperEqualSelectedDescription.branchFootprint]
    omega
  | grouped small source hK hB =>
    have hSource : 0 < source.address := by rw [source.address_correct]; exact binaryWordWidth_pos _
    dsimp only [GeneralPaperEqualSelectedDescription.branchFootprint,GeneralPaperEqualRetainedStorage.footprint]
    omega

theorem inner_nonempty {n : ℕ} (model : RationalCostModel) (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) : (GeneralPaperEqualMeasuredLayout.run model S a).inner ≠ [] := by
  intro hNil
  have hCount := GeneralPaperMeasuredBlockLayout.count model S (innerWidth a) 0 (inner model S a)
  change (GeneralPaperEqualMeasuredLayout.run model S a).inner.length = _ at hCount
  rw [hNil,List.length_nil] at hCount
  have hSizes : (inner model S a).sizes = [] := List.length_eq_zero_iff.mp hCount.symm
  have h := inner_positive model S a
  rw [hSizes,List.sum_nil] at h
  omega

theorem actual_fields {n : ℕ} (model : RationalCostModel) (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) :
    (extract S a.address (GeneralPaperEqualMeasuredLayout.run model S a).outer).1 =
      some (canonical a.address (GeneralPaperEqualMeasuredLayout.run model S a).boundary) :=
  extracted model S a.address (GeneralPaperEqualMeasuredLayout.run model S a).boundary

theorem success {n : ℕ} (model : RationalCostModel) (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) :
    let layout := GeneralPaperEqualMeasuredLayout.run model S a
    let selected := GeneralPaperLastRegionSelection.run S (innerWidth a) layout.inner
    let fields := extract S a.address layout.outer
    ∃ root,root ∈ layout.inner ∧ selected.1 = some root ∧
      (run model S a).1 = some (finish model S (innerWidth a) a.address (layout.work + selected.2 + fields.2)
        (canonical a.address layout.boundary) root (branchTag a)).1 ∧
      (run model S a).2 = (finish model S (innerWidth a) a.address (layout.work + selected.2 + fields.2)
        (canonical a.address layout.boundary) root (branchTag a)).2 := by
  dsimp only
  obtain ⟨root,hRoot⟩ := GeneralPaperLastRegionSelection.nonempty S (innerWidth a)
    (GeneralPaperEqualMeasuredLayout.run model S a).inner (inner_nonempty model S a)
  refine ⟨root,GeneralPaperLastRegionSelection.member S (innerWidth a) _ root hRoot,hRoot,?_,?_⟩
  · simp only [run,hRoot,actual_fields]
  · simp only [run,hRoot,actual_fields]

theorem finish_address_read (model : RationalCostModel) (S I A start baseWork : ℕ)
    (innerRoot : Region I) (tag : ℕ) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A) :
    (GeneralPaperEqualOuterFieldProgram.read_address model A (finish model S I A baseWork (canonical A start) innerRoot tag).1).1 =
      some A :=
  GeneralPaperEqualOuterFieldProgram.address_read model S A start
    (GeneralPaperStoredWordEncoding.word model S A innerRoot.reference.value).1
    (GeneralPaperStoredWordEncoding.word model S A tag).1 hA hCap

theorem finish_field_read (model : RationalCostModel) (S I A start baseWork : ℕ)
    (innerRoot : Region I) (tag : ℕ) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A) (j : Fin 3) :
    (GeneralPaperEqualOuterFieldProgram.read_field model A (finish model S I A baseWork (canonical A start) innerRoot tag).1 j.val).1 =
      some (⟨A,([(GeneralPaperStoredWordEncoding.word model S A innerRoot.reference.value).1,
        (canonical A start).control.reference,(GeneralPaperStoredWordEncoding.word model S A tag).1][j.val]'j.isLt)⟩ : Word) :=
  GeneralPaperEqualOuterFieldProgram.field_read model S A start
    (GeneralPaperStoredWordEncoding.word model S A innerRoot.reference.value).1
    (GeneralPaperStoredWordEncoding.word model S A tag).1 hA hCap j

theorem finish_root (model : RationalCostModel) (S I A baseWork : ℕ) (fields : Fields A) (innerRoot : Region I) (tag : ℕ) :
    (finish model S I A baseWork fields innerRoot tag).1.root = fields.record.reference := rfl

theorem finish_work (model : RationalCostModel) (S I A baseWork : ℕ) (fields : Fields A) (innerRoot : Region I) (tag : ℕ) :
    (finish model S I A baseWork fields innerRoot tag).1.work = (finish model S I A baseWork fields innerRoot tag).2 := rfl

end Blotto.GeneralPaperEqualOuterFieldExtraction
