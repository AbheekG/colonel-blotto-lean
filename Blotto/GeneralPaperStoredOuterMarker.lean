import Blotto.GeneralPaperStoredSelectedConstruction

/-! The branch discriminator is read from the actual outer memory and its
unsigned decoding is priced. Constructor tag correspondence follows from
the real outer writes, independently of inner source correctness. -/
namespace Blotto.GeneralPaperStoredOuterMarker
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualOuterFieldLayout
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

def read (model : RationalCostModel) (A : ℕ) (outer : Installed A) : Option ℕ × ℕ :=
  let field := GeneralPaperStoredOuterRead.field model A outer 2
  match field.1 with
  | none => (none,field.2 + 64 * (A + 1))
  | some ⟨B,tag⟩ => (some tag.value,field.2 + B + 64 * (A + B + 1))

def branchTag {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} : GeneralPaperEqualBitBranch.Prepared v k budget → ℕ
  | .dominant _ _ _ _ => 0
  | .grouped _ _ _ _ => 1

theorem from_field (model : RationalCostModel) (A B tag : ℕ) (outer : Installed A)
    (hField : (GeneralPaperStoredOuterRead.field model A outer 2).1 = some (⟨B,FixedBinaryWord.ofNat B tag⟩ : Word))
    (hTag : tag < 2 ^ B) :
    (read model A outer).1 = some tag ∧ (read model A outer).2 =
      (GeneralPaperStoredOuterRead.field model A outer 2).2 + B + 64 * (A + B + 1) := by
  simp only [read,hField,FixedBinaryWord.value_ofNat B tag hTag,and_self]

theorem attached (model : RationalCostModel) (S I A start prefixWork tag : ℕ) (inner : Installed I)
    (hA : 0 < A) (hCap : start + (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A)
    (hTag : tag < 2 ^ A) :
    (read model A (GeneralPaperStoredOuterAttachment.finish model S I A prefixWork (canonical A start) inner tag)).1 = some tag := by
  have hRead := GeneralPaperStoredOuterAttachment.outer_readback model S I A start prefixWork inner tag hA hCap
  have hField := GeneralPaperStoredOuterRead.field_source model A _ (canonical A start) _ _ hRead rfl ⟨2,by decide⟩
  exact (from_field model A A tag _ hField hTag).1

theorem grouped_return {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (model : RationalCostModel) (S : ℕ) (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S (sampler.address + 1)).sizes.sum < 2 ^ (sampler.address + 1))
    (returned : Installed (sampler.address + 1))
    (hReturn : (GeneralPaperStoredGroupedOuterConstruction.run model S sampler).values = some returned) :
    (read model (sampler.address + 1) returned).1 = some 1 := by
  simp only [GeneralPaperStoredGroupedOuterConstruction.run,GeneralPaperStoredGroupedOuterConstruction.fields_source] at hReturn
  cases hInner : (GeneralPaperCountedSamplerInstallation.run model S sampler.address sampler
      (GeneralPaperStoredGroupedOuterConstruction.layout model S sampler).inner).values with
  | none => simp only [hInner] at hReturn; cases hReturn
  | some inner =>
    simp only [hInner] at hReturn
    rw [← Option.some.inj hReturn]
    apply attached model S sampler.address (sampler.address + 1) _ _ 1 inner (by omega)
    · simpa only [GeneralPaperStoredGroupedOuterConstruction.layout,GeneralPaperMeasuredTwoPoolLayout.boundary] using hCap
    · have h := Nat.two_pow_pos sampler.address
      rw [pow_succ]
      omega

theorem dominant_return {n : ℕ} (model : RationalCostModel) (S A chosen : ℕ) (row : RationalResourceArray n)
    (hA : 0 < A) (hCap : (GeneralPaperStoredDominantCursor.plan model S A chosen row).sizes.sum +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A)
    (returned : Installed A) (hReturn : (GeneralPaperStoredDominantOuterConstruction.run model S A chosen row).values = some returned) :
    (read model A returned).1 = some 0 := by
  simp only [GeneralPaperStoredDominantOuterConstruction.run,GeneralPaperStoredDominantOuterConstruction.fields_source] at hReturn
  cases hInner : (GeneralPaperStoredDominantInstallation.run model S A chosen row
      (GeneralPaperStoredDominantOuterConstruction.layout model S A chosen row).inner).values with
  | none => simp only [hInner] at hReturn; cases hReturn
  | some inner =>
    simp only [hInner] at hReturn
    rw [← Option.some.inj hReturn]
    apply attached model S A A _ _ 0 inner hA
    · simpa only [GeneralPaperStoredDominantOuterConstruction.layout,GeneralPaperMeasuredTwoPoolLayout.boundary] using hCap
    · exact Nat.two_pow_pos A

theorem selected_return {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : GeneralPaperEqualSelectedSampler.Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (returned : Installed a.address) (hReturn : (GeneralPaperStoredSelectedConstruction.run model S a).1 = some returned) :
    (read model a.address returned).1 = some (branchTag a.branch) := by
  rcases a with ⟨branch,A,hAddress⟩
  cases branch with
  | dominant chosen heavy row correct =>
    let a : GeneralPaperEqualSelectedSampler.Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget :=
      ⟨.dominant chosen heavy row correct,A,hAddress⟩
    obtain ⟨hA,_,hCap⟩ := GeneralPaperStoredDominantOuterContract.bounds model W S k values v hv budget a chosen heavy row correct rfl
    exact dominant_return model S A chosen.val row hA hCap returned hReturn
  | grouped small sampler hK hB =>
    dsimp only [GeneralPaperEqualSelectedSampler.baseReference] at hAddress
    subst A
    let a : GeneralPaperEqualSelectedSampler.Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget :=
      ⟨.grouped small sampler hK hB,sampler.address + 1,rfl⟩
    have hCap := GeneralPaperEqualMeasuredLayout.total_capacity model W S k values v hv budget a
    have hActual : (GeneralPaperStoredGroupedOuterConstruction.run model S sampler).values = some returned := by
      change Option.map (fun value : Installed (sampler.address + 1) => value)
        (GeneralPaperStoredGroupedOuterConstruction.run model S sampler).values = some returned at hReturn
      simpa using hReturn
    exact grouped_return model S sampler hCap returned hActual

end Blotto.GeneralPaperStoredOuterMarker
