import Blotto.GeneralPaperEqualInnerRecordRoot

/-! Actual native outer extraction succeeds. The same returned RAM/root
recovers its stored address, branch marker and pointer to the actual inner
reserved record. Initialized-source and copied-return endpoints use this
constructor directly; final inner payload/draw/resource joins remain open. -/
namespace Blotto.GeneralPaperEqualOuterNativeContract
open GeneralPaperEqualMeasuredLayout GeneralPaperEqualSelectedSampler GeneralPaperEqualOuterFieldLayout
open GeneralPaperEqualOuterFieldExtraction GeneralPaperSequentialLayout
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

theorem tag_fits {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (a : Sampler v k budget) :
    branchTag a < 2 ^ a.address := by
  have hTag : branchTag a ≤ 1 := by unfold branchTag; split <;> omega
  have hPow : 2 ≤ 2 ^ a.address := by
    have h := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (widths_positive a).2
    simpa only [pow_one] using h
  omega

theorem native {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    ∃ root ∈ (GeneralPaperEqualMeasuredLayout.run model S a).inner,
      ∃ output : GeneralPaperEqualOuterFieldProgram.Installed a.address,
        (GeneralPaperEqualOuterFieldExtraction.run model S a).1 = some output ∧
        output.work = (GeneralPaperEqualOuterFieldExtraction.run model S a).2 ∧
        output.root = (canonical a.address (GeneralPaperEqualMeasuredLayout.run model S a).boundary).record.reference ∧
        (GeneralPaperEqualOuterFieldProgram.read_address model a.address output).1 = some a.address ∧
        (GeneralPaperEqualOuterFieldProgram.read_field model a.address output 0).1 =
          some (⟨a.address,FixedBinaryWord.ofNat a.address root.start⟩ : Word) ∧
        (GeneralPaperEqualOuterFieldProgram.read_field model a.address output 2).1 =
          some (⟨a.address,FixedBinaryWord.ofNat a.address (branchTag a)⟩ : Word) ∧
        (FixedBinaryWord.ofNat a.address (branchTag a)).value = branchTag a ∧
        root.length = GeneralPaperEqualInnerRecordRoot.arity a * innerWidth a := by
  obtain ⟨root,hMem,hSelected,hRun,hWork⟩ := success model S a
  let layout := GeneralPaperEqualMeasuredLayout.run model S a
  let selected := GeneralPaperLastRegionSelection.run S (innerWidth a) layout.inner
  let fields := extract S a.address layout.outer
  let baseWork := layout.work + selected.2 + fields.2
  let output := (finish model S (innerWidth a) a.address baseWork (canonical a.address layout.boundary) root (branchTag a)).1
  have hCap := GeneralPaperEqualReferencePoolInstallation.outer_capacity model W S k values v hv budget a
  have hA : 0 < a.address := (widths_positive a).2
  have hValue := (GeneralPaperEqualInnerRecordRoot.native_reference model W S k values v hv budget a root hMem).1
  have hAddress := finish_address_read model S (innerWidth a) a.address layout.boundary baseWork root (branchTag a) hA hCap
  have hBranch := finish_field_read model S (innerWidth a) a.address layout.boundary baseWork root (branchTag a) hA hCap ⟨0,by decide⟩
  have hTag := finish_field_read model S (innerWidth a) a.address layout.boundary baseWork root (branchTag a) hA hCap ⟨2,by decide⟩
  refine ⟨root,hMem,output,hRun,?_,finish_root model S (innerWidth a) a.address baseWork _ root (branchTag a),
    hAddress,?_,?_,FixedBinaryWord.value_ofNat a.address (branchTag a) (tag_fits a),
    GeneralPaperEqualInnerRecordRoot.selected_length model S a root hSelected⟩
  · exact (finish_work model S (innerWidth a) a.address baseWork _ root (branchTag a)).trans hWork.symm
  · simpa only [GeneralPaperStoredWordEncoding.word_data,hValue,List.getElem_cons_zero] using hBranch
  · simpa only [GeneralPaperStoredWordEncoding.word_data,List.getElem_cons_succ,List.getElem_cons_zero] using hTag

theorem every_return_address {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (returned : GeneralPaperEqualOuterFieldProgram.Installed a.address)
    (hReturn : (GeneralPaperEqualOuterFieldExtraction.run model S a).1 = some returned) :
    (GeneralPaperEqualOuterFieldProgram.read_address model a.address returned).1 = some a.address ∧
      returned.work = (GeneralPaperEqualOuterFieldExtraction.run model S a).2 := by
  obtain ⟨_,_,output,hRun,hWork,_,hAddress,_⟩ := native model W S k values v hv budget a
  have hEq : output = returned := Option.some.inj (hRun.symm.trans hReturn)
  rw [← hEq]
  exact ⟨hAddress,hWork⟩

theorem actual_initialized_source (model : RationalCostModel) (A K : ℕ) (p : GeneralPaperEqualInputDomain.Input model) :
    let W := GeneralPaperEqualInputDomain.word K p
    let a := (GeneralPaperEqualSelectedPipeline.run model A K p).1
    ∃ output : GeneralPaperEqualOuterFieldProgram.Installed a.address,
      (GeneralPaperEqualOuterFieldExtraction.run model W a).1 = some output ∧
      (GeneralPaperEqualOuterFieldProgram.read_address model a.address output).1 = some a.address ∧
      output.work = (GeneralPaperEqualOuterFieldExtraction.run model W a).2 := by
  dsimp only
  obtain ⟨_,_,output,hRun,hWork,_,hAddress,_⟩ := native model (GeneralPaperEqualInputDomain.word K p)
    (GeneralPaperEqualInputDomain.word K p) p.k p.values p.selector p.correct p.budget
    (GeneralPaperEqualSelectedPipeline.run model A K p).1
  exact ⟨output,hRun,hAddress,hWork⟩

theorem actual_copied_return (model : RationalCostModel) (A K : ℕ) (p : GeneralPaperEqualInputDomain.Input model) :
    let W := GeneralPaperEqualInputDomain.word K p
    let a := (GeneralPaperEqualCopiedPipeline.run model A K p).1
    ∃ output : GeneralPaperEqualOuterFieldProgram.Installed a.address,
      (GeneralPaperEqualOuterFieldExtraction.run model W a).1 = some output ∧
      (GeneralPaperEqualOuterFieldProgram.read_address model a.address output).1 = some a.address ∧
      output.work = (GeneralPaperEqualOuterFieldExtraction.run model W a).2 := by
  dsimp only
  rw [GeneralPaperEqualCopiedPipeline.selected_data]
  exact actual_initialized_source model A K p

end Blotto.GeneralPaperEqualOuterNativeContract
