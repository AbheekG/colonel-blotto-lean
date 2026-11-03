import Blotto.GeneralPaperReferenceHeaderProgram
import Blotto.GeneralPaperEqualMeasuredPlanPositive

/-! Measured array/list extents derive the header-installation premises.
The dominant selected branch supplies its header capacity directly from the
actual native description. Installed targets are read by computed local
indices; correspondence of target words to child payloads is joined later. -/
namespace Blotto.GeneralPaperMeasuredHeaderInstallation
open GeneralPaperMeasuredBlockPlan GeneralPaperEncodedBasisStorage
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

theorem array_cap {α : Type*} {n : ℕ} (model : RationalCostModel) (S A base : ℕ) (measure : α → Plan)
    (source : FixedArrayTable n α) (hCap : base + (GeneralPaperMeasuredArrayBlockPlan.array model S A measure source).sizes.sum < 2 ^ A) :
    base + A * (64 + n) < 2 ^ A := by
  rw [GeneralPaperMeasuredArrayBlockPlan.array_data,List.sum_append] at hCap
  simp only [List.sum_cons,List.sum_nil,Nat.add_zero] at hCap
  have hEq : A * (n + 64) = A * (64 + n) := by ring
  omega

theorem list_cap {α : Type*} (model : RationalCostModel) (S A base stride fixed : ℕ) (measure : α → Plan)
    (xs : List α) (hCap : base + (GeneralPaperMeasuredListBlockPlan.run model S A stride fixed measure xs).sizes.sum < 2 ^ A) :
    base + A * (fixed + stride * xs.length) < 2 ^ A := by
  rw [GeneralPaperMeasuredListBlockPlan.data,List.sum_append] at hCap
  simp only [List.sum_cons,List.sum_nil,Nat.add_zero] at hCap
  have hEq : A * (stride * xs.length + fixed) = A * (fixed + stride * xs.length) := by ring
  omega

theorem array_read {α : Type*} {n : ℕ} (model : RationalCostModel) (S A base : ℕ) (measure : α → Plan)
    (source : FixedArrayTable n α) (pointers : List (FixedBinaryWord A)) (hPointers : pointers.length = n)
    (memory : GeneralPaperRawReferenceMemory.Memory A) (hA : 0 < A)
    (hCap : base + (GeneralPaperMeasuredArrayBlockPlan.array model S A measure source).sizes.sum < 2 ^ A) (j : Fin n) :
    (GeneralPaperReferenceHeaderProgram.read model A
      (GeneralPaperReferenceHeaderProgram.prepare model S A base 64 1 0 pointers memory).memory base 64 1 j.val 0).1 =
      some (pointers[j.val]'(by rw [hPointers]; exact j.isLt)) := by
  have hHeader := array_cap model S A base measure source hCap
  have hTarget : base + A * (64 + 1 * pointers.length) < 2 ^ A := by simpa only [hPointers,one_mul] using hHeader
  exact GeneralPaperReferenceHeaderProgram.read_prepared model S A base 64 1 0 pointers memory hA (by decide) hTarget
    ⟨j.val,by rw [hPointers]; exact j.isLt⟩

theorem list_read {α : Type*} (model : RationalCostModel) (S A base stride fixed cell : ℕ) (measure : α → Plan)
    (xs : List α) (pointers : List (FixedBinaryWord A)) (hPointers : pointers.length = xs.length)
    (memory : GeneralPaperRawReferenceMemory.Memory A) (hA : 0 < A) (hCell : cell < stride)
    (hCap : base + (GeneralPaperMeasuredListBlockPlan.run model S A stride fixed measure xs).sizes.sum < 2 ^ A)
    (j : Fin xs.length) :
    (GeneralPaperReferenceHeaderProgram.read model A
      (GeneralPaperReferenceHeaderProgram.prepare model S A base fixed stride cell pointers memory).memory
      base fixed stride j.val cell).1 = some (pointers[j.val]'(by rw [hPointers]; exact j.isLt)) := by
  have hHeader := list_cap model S A base stride fixed measure xs hCap
  have hTarget : base + A * (fixed + stride * pointers.length) < 2 ^ A := by simpa only [hPointers] using hHeader
  exact GeneralPaperReferenceHeaderProgram.read_prepared model S A base fixed stride cell pointers memory hA hCell hTarget
    ⟨j.val,by rw [hPointers]; exact j.isLt⟩

theorem dominant_read {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : GeneralPaperEqualSelectedSampler.Sampler
      (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (chosen : Fin n) (heavy : 1 / 2 ≤ (GeneralPaperEqualNativeSampler.rounded true model W k values v hv).weight chosen)
    (source : RationalResourceArray n) (correct : source.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen)
    (hBranch : a.branch = .dominant chosen heavy source correct) (pointers : List (FixedBinaryWord a.address))
    (hPointers : pointers.length = n) (memory : GeneralPaperRawReferenceMemory.Memory a.address) (j : Fin n) :
    (GeneralPaperReferenceHeaderProgram.read model a.address
      (GeneralPaperReferenceHeaderProgram.prepare model S a.address 0 64 1 0 pointers memory).memory 0 64 1 j.val 0).1 =
      some (pointers[j.val]'(by rw [hPointers]; exact j.isLt)) := by
  have hFull := GeneralPaperEqualSelectedDescription.capacity model W k values v hv budget a
  have hArray : arrayFootprint a.address rationalWordWidth (⟨source.data,source.size⟩ : FixedArrayTable n ℚ) =
      64 * a.address + n * a.address + ∑ i : Fin n,rationalWordWidth (source.allocation i) := by
    unfold arrayFootprint
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
    change 64 * a.address + (n * a.address + ∑ i : Fin n,rationalWordWidth (source.allocation i)) = _
    ring
  dsimp only [GeneralPaperEqualSelectedDescription.footprint] at hFull
  rw [hBranch] at hFull
  dsimp only [GeneralPaperEqualSelectedDescription.branchFootprint] at hFull
  rw [hArray] at hFull
  have hHeader : 0 + a.address * (64 + 1 * pointers.length) < 2 ^ a.address := by
    rw [hPointers]
    have hEq : 0 + a.address * (64 + 1 * n) = 64 * a.address + n * a.address := by ring
    rw [hEq]
    omega
  exact GeneralPaperReferenceHeaderProgram.read_prepared model S a.address 0 64 1 0 pointers memory
    (GeneralPaperEqualMeasuredLayout.widths_positive a).2 (by decide) hHeader ⟨j.val,by rw [hPointers]; exact j.isLt⟩

end Blotto.GeneralPaperMeasuredHeaderInstallation
