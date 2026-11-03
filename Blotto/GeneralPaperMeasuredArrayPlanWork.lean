import Blotto.GeneralPaperMeasuredLeafPlanWork

/-! Complete executed indexed-array plan prices include every callback,
array descriptor/index/reference step, flattening pass, header measurement
and final append. Payload lengths add; a worst scalar is never multiplied by
the number of entries. -/
namespace Blotto.GeneralPaperMeasuredArrayPlanWork
open GeneralPaperMeasuredBlockPlan GeneralPaperMeasuredPlanWorkAlgebra
open GeneralPaperEncodedScalarStorage (natBits)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 8192

theorem singleton_append (model : RationalCostModel) (S A size : ℕ) (ys : List ℕ)
    (hA : 0 < A) (hCap : size < 2 ^ A) : (append S [size] ys).2 ≤ unit model S A := by
  have hw := binaryWordWidth_le_of_lt_pow hA hCap
  have hU := unit_bounds model S A
  rw [GeneralPaperMeasuredBlockPlan.append_work]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  unfold natBits
  omega

theorem flatten_work (model : RationalCostModel) (S A : ℕ) (xss : List (List ℕ))
    (hA : 0 < A) (hPos : ∀ xs ∈ xss,∀ size ∈ xs,0 < size)
    (hCap : ∀ xs ∈ xss,xs.sum < 2 ^ A) :
    (GeneralPaperMeasuredArrayBlockPlan.flatten S xss).2 ≤
      ((xss.map List.sum).sum + 2 * xss.length + 1) * unit model S A := by
  induction xss with
  | nil =>
    change 64 * S + 64 ≤ (0 + 2 * 0 + 1) * unit model S A
    have h := unit_bounds model S A
    omega
  | cons xs xss ih =>
    have hh : xs ∈ xs :: xss := List.mem_cons_self ..
    have hAppend := GeneralPaperMeasuredPlanWorkAlgebra.append_work model S A xs
      (GeneralPaperMeasuredArrayBlockPlan.flatten S xss).1 hA (hPos xs hh) (hCap xs hh)
    have ht := ih (fun ys hy => hPos ys (List.mem_cons_of_mem _ hy)) (fun ys hy => hCap ys (List.mem_cons_of_mem _ hy))
    have hU : 64 * S + 64 ≤ unit model S A := by have h := unit_bounds model S A; omega
    change _ + _ + 64 * S + 64 ≤ _
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith only [hAppend,ht,hU]

theorem area {α : Type*} {n : ℕ} (model : RationalCostModel) (S A : ℕ) (measure : α → Plan)
    (source : FixedArrayTable n α) :
    (GeneralPaperMeasuredArrayBlockPlan.array model S A measure source).sizes.sum =
      A * (n + 64) + ∑ j : Fin n,(measure (source.read j)).sizes.sum := by
  rw [GeneralPaperMeasuredArrayBlockPlan.array_sum model S A measure (fun x => (measure x).sizes.sum) source (fun _ => rfl)]
  unfold GeneralPaperEncodedBasisStorage.arrayFootprint
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  ring

theorem array {α : Type*} {n : ℕ} (model : RationalCostModel) (S A C : ℕ) (measure : α → Plan)
    (source : FixedArrayTable n α) (hA : 0 < A) (hGood : ∀ j,Good model S A C (measure (source.read j))) :
    Good model S A (C + 8) (GeneralPaperMeasuredArrayBlockPlan.array model S A measure source) := by
  refine ⟨GeneralPaperMeasuredPlanPositive.array model S A measure source hA (fun j => (hGood j).1),?_⟩
  intro hCap
  rw [area] at hCap ⊢
  let P := ∑ j : Fin n,(measure (source.read j)).sizes.sum
  have hArea : A * (n + 64) + P < 2 ^ A := hCap
  have hN : n ≤ A * (n + 64) := by
    have h := Nat.mul_le_mul_right (n + 64) hA
    nlinarith only [h]
  have hHeader : A * (n + 64) < 2 ^ A := by omega
  have hCount := binaryWordWidth_le_of_lt_pow hA (show n < 2 ^ A by omega)
  have hAdd := GeneralPaperRayOperandWidthEnvelope.word_add n 1
  have hOne : binaryWordWidth 1 = 1 := by decide
  have hIndex : binaryWordWidth (n + 1) ≤ A + 8 := by omega
  have hChildCap : ∀ j,(measure (source.read j)).sizes.sum < 2 ^ A := by
    intro j
    have h := Finset.single_le_sum (f := fun i : Fin n => (measure (source.read i)).sizes.sum)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    change (measure (source.read j)).sizes.sum ≤ P at h
    omega
  have hChildWork : (∑ j : Fin n,(measure (source.read j)).work) ≤ (P + n) * C * unit model S A := by
    calc
      _ ≤ ∑ j : Fin n,((measure (source.read j)).sizes.sum + 1) * C * unit model S A :=
        Finset.sum_le_sum (fun j _ => (hGood j).2 (hChildCap j))
      _ = _ := by
        have he : (∑ j : Fin n,((measure (source.read j)).sizes.sum + 1) * C * unit model S A) =
            (∑ j : Fin n,((measure (source.read j)).sizes.sum + 1)) * C * unit model S A := by
          rw [Finset.sum_mul,Finset.sum_mul]
        rw [he,Finset.sum_add_distrib]
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.mul_one]
        rfl
  let callback := fun j : Fin n => ((measure (source.read j)).sizes,(measure (source.read j)).work + 32 * S + 32)
  let measured := PaperIndexedArrayConstruction.run id S callback
  have hMeasured := PaperIndexedArrayConstruction.run_work_bound id 1 (fun w => by change w ≤ 1 * w; omega) S callback
  have hLoop : 6 * S + 10 * 1 * binaryWordWidth (n + 1) + 28 ≤ unit model S A := by unfold unit; omega
  have hLoopTotal := Nat.mul_le_mul_left (n + 1) hLoop
  have hEachControl : 32 * S + 32 ≤ unit model S A := by have h := unit_bounds model S A; omega
  have hControl := Nat.mul_le_mul_left n hEachControl
  change measured.2 ≤ _ at hMeasured
  dsimp only [callback] at hMeasured
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at hMeasured
  have hData : measured.1.data.toList = List.ofFn (fun j : Fin n => (measure (source.read j)).sizes) := by
    simp only [measured,PaperIndexedArrayConstruction.run_data,callback,FixedArrayTable.ofFn,Array.toList_ofFn]
  have hFlat := flatten_work model S A (List.ofFn (fun j : Fin n => (measure (source.read j)).sizes)) hA
    (by intro xs hx; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx; exact (hGood j).1)
    (by intro xs hx; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx; exact hChildCap j)
  simp only [List.map_ofFn,List.sum_ofFn,List.length_ofFn,Function.comp_def] at hFlat
  change (GeneralPaperMeasuredArrayBlockPlan.flatten S _).2 ≤ (P + 2 * n + 1) * unit model S A at hFlat
  rw [← hData] at hFlat
  have hHeaderWork := GeneralPaperMeasuredLeafPlanWork.references_work model S A n 1 64
    (by omega) (by change 1 ≤ A + 8; omega) (by change 7 ≤ A + 8; omega)
  have hAppend := singleton_append model S A (A * (n + 64))
    (GeneralPaperMeasuredArrayBlockPlan.flatten S measured.1.data.toList).1 hA hHeader
  have hBase : 64 * S + 64 ≤ unit model S A := by have h := unit_bounds model S A; omega
  have hP := Nat.mul_le_mul_right (C * unit model S A) (show P + n ≤ A * (n + 64) + P + 1 by omega)
  have hOther := Nat.mul_le_mul_right (unit model S A) (show P + 4 * n + 6 ≤ 8 * (A * (n + 64) + P + 1) by omega)
  unfold GeneralPaperMeasuredArrayBlockPlan.array GeneralPaperMeasuredBlockPlan.join
  simp only [source.size,GeneralPaperMeasuredBlockPlan.references_data,Nat.one_mul]
  change (GeneralPaperMeasuredBlockPlan.references model S A n 1 64).work +
    (measured.2 + (GeneralPaperMeasuredArrayBlockPlan.flatten S measured.1.data.toList).2 + 64 * S + 64) +
    (append S [A * (n + 64)] (GeneralPaperMeasuredArrayBlockPlan.flatten S measured.1.data.toList).1).2 + 64 * S + 64 ≤ _
  dsimp only [P] at hChildWork hFlat hP hOther
  nlinarith only [hChildWork,hMeasured,hLoopTotal,hControl,hFlat,hHeaderWork,hAppend,hBase,hP,hOther]

end Blotto.GeneralPaperMeasuredArrayPlanWork
