import Blotto.GeneralPaperMeasuredLayoutComposition

/-! The dominant native branch installs its row from the corresponding
prefix of its complete measured branch layout. Capacity is derived from the
native selected description. Actual local-pointer reads recover its rational
allocation coordinates, with no source-value or target-root oracle at read. -/
namespace Blotto.GeneralPaperEqualDominantLayoutAccess
open GeneralPaperMeasuredBlockPlan GeneralPaperSequentialLayout
open GeneralPaperEqualSelectedSampler (Sampler)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def rowTable {n : ℕ} (source : RationalResourceArray n) : FixedArrayTable n ℚ := ⟨source.data,source.size⟩

def regions {n : ℕ} (model : RationalCostModel) (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) : List (Region a.address) :=
  ((GeneralPaperMeasuredBlockLayout.run model S a.address 0
    (GeneralPaperEqualMeasuredLayout.inner model S a)).1.take (n + 1)).tail

def prepare {n : ℕ} (model : RationalCostModel) (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) (source : RationalResourceArray n) : GeneralPaperScalarArrayReferenceProgram.Prepared a.address ℚ :=
  let actualLayout := GeneralPaperMeasuredBlockLayout.run model S a.address 0 (GeneralPaperEqualMeasuredLayout.inner model S a)
  let actual := GeneralPaperScalarArrayReferenceProgram.install model S a.address 0 rationalWordWidth
    (rowTable source) ((actualLayout.1.take (n + 1)).tail)
  ⟨actual.references,actual.payloads,actualLayout.2.2 + actual.work + 64 * (S + a.address + 1)⟩

theorem branch_data {n : ℕ} (model : RationalCostModel) (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) (chosen : Fin n) (heavy : 1 / 2 ≤ v.weight chosen)
    (source : RationalResourceArray n) (correct : source.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen)
    (hBranch : a.branch = .dominant chosen heavy source correct) :
    (GeneralPaperEqualMeasuredLayout.inner model S a).sizes =
      (GeneralPaperScalarArrayLayout.plan model S a.address (rational model S) (rowTable source)).sizes ++
        [GeneralPaperEncodedScalarStorage.natBits chosen.val,32 * a.address] := by
  unfold GeneralPaperEqualMeasuredLayout.inner
  rw [hBranch]
  simp only [GeneralPaperEqualMeasuredSelectedPlan.branch,sequence_data,List.map_cons,List.map_nil,List.flatten_cons,
    List.flatten_nil,natural_data,GeneralPaperEqualMeasuredLeafPlans.reserve,references_data,Nat.mul_zero,Nat.zero_add,
    List.singleton_append,List.append_nil]
  rw [Nat.mul_comm a.address 32]
  rfl

theorem actual_payloads {n : ℕ} (model : RationalCostModel) (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) (chosen : Fin n) (heavy : 1 / 2 ≤ v.weight chosen)
    (source : RationalResourceArray n) (correct : source.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen)
    (hBranch : a.branch = .dominant chosen heavy source correct) :
    regions model S a = GeneralPaperScalarArrayLayout.payloads model S a.address 0 (rational model S) (rowTable source) := by
  have hCount : (GeneralPaperScalarArrayLayout.plan model S a.address (rational model S) (rowTable source)).sizes.length = n + 1 := by
    rw [GeneralPaperScalarArrayLayout.plan_data model S a.address (rational model S) rationalWordWidth (rowTable source)
      (rational_data model S)]
    simp only [List.length_cons,List.length_map,Array.length_toList,(rowTable source).size]
  unfold regions GeneralPaperMeasuredBlockLayout.run
  rw [branch_data model S a chosen heavy source correct hBranch,← hCount,
    GeneralPaperMeasuredLayoutComposition.first_regions]
  rfl

theorem capacity {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (chosen : Fin n) (heavy : 1 / 2 ≤ (GeneralPaperEqualNativeSampler.rounded true model W k values v hv).weight chosen)
    (source : RationalResourceArray n) (correct : source.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen)
    (hBranch : a.branch = .dominant chosen heavy source correct) :
    0 + (GeneralPaperScalarArrayLayout.plan model S a.address (rational model S) (rowTable source)).sizes.sum < 2 ^ a.address := by
  have h := GeneralPaperEqualMeasuredLayout.inner_capacity model W S k values v hv budget a
  have hWidth : GeneralPaperEqualMeasuredLayout.innerWidth a = a.address := by
    unfold GeneralPaperEqualMeasuredLayout.innerWidth
    rw [hBranch]
  rw [hWidth,branch_data model S a chosen heavy source correct hBranch,List.sum_append] at h
  omega

theorem read_source {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (chosen : Fin n) (heavy : 1 / 2 ≤ (GeneralPaperEqualNativeSampler.rounded true model W k values v hv).weight chosen)
    (source : RationalResourceArray n) (correct : source.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen)
    (hBranch : a.branch = .dominant chosen heavy source correct) (j : Fin n) :
    (GeneralPaperScalarArrayReferenceProgram.read model a.address rationalWordWidth (prepare model S a source)
      (FixedBinaryWord.ofNat a.address 0) j.val).1 = some (source.allocation j) := by
  have hCap := capacity model W S k values v hv budget a chosen heavy source correct hBranch
  have hRegions := actual_payloads model S a chosen heavy source correct hBranch
  have hCount := GeneralPaperScalarArrayLayout.payload_count model S a.address 0 (rational model S) rationalWordWidth
    (rowTable source) (rational_data model S)
  have hKeys := GeneralPaperScalarArrayLayout.payload_keys model S a.address 0 (rational model S) rationalWordWidth
    (rowTable source) (rational_data model S) (fun q => by have h := GeneralPaperEqualNativeDrawRepresentation.budget_width q; omega) hCap
  rw [← hRegions] at hCount hKeys
  have h := GeneralPaperScalarArrayReferenceProgram.install_read model S a.address 0 rationalWordWidth (rowTable source)
    (regions model S a) hCount hKeys (GeneralPaperEqualMeasuredLayout.widths_positive a).2
    (GeneralPaperMeasuredHeaderInstallation.array_cap model S a.address 0 (rational model S) (rowTable source) hCap) j
  exact h

theorem read_vertex {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (chosen : Fin n) (heavy : 1 / 2 ≤ (GeneralPaperEqualNativeSampler.rounded true model W k values v hv).weight chosen)
    (source : RationalResourceArray n) (correct : source.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen)
    (hBranch : a.branch = .dominant chosen heavy source correct) (j : Fin n) :
    (GeneralPaperScalarArrayReferenceProgram.read model a.address rationalWordWidth (prepare model S a source)
      (FixedBinaryWord.ofNat a.address 0) j.val).1 = some (if j = chosen then budget else 0) := by
  rw [read_source model W S k values v hv budget a chosen heavy source correct hBranch j,
    GeneralPaperEqualBitCanonical.pure_coordinates budget chosen source correct]

theorem read_work {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (chosen : Fin n) (heavy : 1 / 2 ≤ (GeneralPaperEqualNativeSampler.rounded true model W k values v hv).weight chosen)
    (source : RationalResourceArray n) (correct : source.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen)
    (hBranch : a.branch = .dominant chosen heavy source correct) (j : Fin n) :
    (GeneralPaperScalarArrayReferenceProgram.read model a.address rationalWordWidth (prepare model S a source)
      (FixedBinaryWord.ofNat a.address 0) j.val).2 =
      (GeneralPaperReferenceHeaderProgram.read model a.address (prepare model S a source).references 0 64 1 j.val 0).2 +
        rationalWordWidth (source.allocation j) + 128 * a.address + 128 := by
  have h := GeneralPaperScalarArrayReferenceProgram.read_work_of_some model a.address rationalWordWidth (prepare model S a source)
    (FixedBinaryWord.ofNat a.address 0) j.val (source.allocation j)
    (read_source model W S k values v hv budget a chosen heavy source correct hBranch j)
  simpa only [FixedBinaryWord.value_ofNat a.address 0 (by positivity)] using h

end Blotto.GeneralPaperEqualDominantLayoutAccess
