import Blotto.GeneralPaperEqualOuterFieldExtraction

/-! The selected final inner region is the branch's reserved record block.
Its actual native references fit both the stored inner word and the wider
outer word; the outer pointer is encoded from this actual region's root. -/
namespace Blotto.GeneralPaperEqualInnerRecordRoot
open GeneralPaperEqualMeasuredLayout GeneralPaperEqualSelectedSampler GeneralPaperSequentialLayout
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def arity {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (a : Sampler v k budget) : ℕ :=
  match a.branch with | .dominant _ _ _ _ => 32 | .grouped _ _ _ _ => 64

theorem last_size {n : ℕ} (model : RationalCostModel) (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) :
    (inner model S a).sizes.getLast? = some (arity a * innerWidth a) := by
  cases a with
  | mk branch A hAddress =>
    cases branch with
    | dominant chosen heavy source correct =>
      simp only [GeneralPaperEqualMeasuredLayout.inner,GeneralPaperEqualMeasuredSelectedPlan.branch,
        GeneralPaperMeasuredBlockPlan.sequence_data,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,
        GeneralPaperEqualMeasuredLeafPlans.reserve,GeneralPaperMeasuredBlockPlan.references_data,arity,innerWidth]
      simp only [List.getLast?_append,List.getLast?_cons,List.getLast?_nil,Option.getD_none,Option.none_or,Option.some_or]
      apply congrArg some
      ring
    | grouped small source hK hB =>
      simp only [GeneralPaperEqualMeasuredLayout.inner,GeneralPaperEqualMeasuredSelectedPlan.branch,
        GeneralPaperEqualMeasuredRetainedPlan.sampler,GeneralPaperMeasuredBlockPlan.sequence_data,
        List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil,GeneralPaperEqualMeasuredLeafPlans.reserve,
        GeneralPaperMeasuredBlockPlan.references_data,arity,innerWidth]
      simp only [List.getLast?_append,List.getLast?_cons,List.getLast?_nil,Option.getD_none,Option.none_or,Option.some_or]
      apply congrArg some
      ring

theorem selected_length {n : ℕ} (model : RationalCostModel) (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) (root : Region (innerWidth a))
    (hRoot : (GeneralPaperLastRegionSelection.run S (innerWidth a) (GeneralPaperEqualMeasuredLayout.run model S a).inner).1 = some root) :
    root.length = arity a * innerWidth a := by
  have hLengths := GeneralPaperMeasuredTwoPoolLayout.inner_lengths model S (innerWidth a) a.address (inner model S a) (outer model S a)
  change (GeneralPaperEqualMeasuredLayout.run model S a).inner.map Region.length = _ at hLengths
  have h := congrArg List.getLast? hLengths
  rw [List.getLast?_map,← GeneralPaperLastRegionSelection.data S (innerWidth a),hRoot,last_size] at h
  exact Option.some.inj h

theorem native_reference {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (root : Region (innerWidth a)) (hRoot : root ∈ (GeneralPaperEqualMeasuredLayout.run model S a).inner) :
    root.reference.value = root.start ∧ root.stop ≤ (GeneralPaperEqualMeasuredLayout.run model S a).boundary ∧
      root.reference.value < 2 ^ innerWidth a ∧ root.reference.value < 2 ^ a.address := by
  have hValue := (references model W S k values v hv budget a).1 root hRoot
  have hRange := GeneralPaperMeasuredBlockLayout.range model S (innerWidth a) 0 (inner model S a) root hRoot
  have hInner := inner_capacity model W S k values v hv budget a
  have hTotal := total_capacity model W S k values v hv budget a
  have hBoundary : (GeneralPaperEqualMeasuredLayout.run model S a).boundary = (inner model S a).sizes.sum :=
    GeneralPaperMeasuredTwoPoolLayout.boundary model S (innerWidth a) a.address (inner model S a) (outer model S a)
  rw [hBoundary]
  unfold Region.stop at hRange ⊢
  simp only [Nat.zero_add] at hRange
  refine ⟨hValue,hRange.2,?_,?_⟩ <;> rw [hValue] <;> omega

theorem native_outer_encoding {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (root : Region (innerWidth a)) (hRoot : root ∈ (GeneralPaperEqualMeasuredLayout.run model S a).inner) :
    (GeneralPaperStoredWordEncoding.word model S a.address root.reference.value).1.value = root.start := by
  have h := native_reference model W S k values v hv budget a root hRoot
  rw [GeneralPaperStoredWordEncoding.word_data,FixedBinaryWord.value_ofNat a.address root.reference.value h.2.2.2,h.1]

end Blotto.GeneralPaperEqualInnerRecordRoot
