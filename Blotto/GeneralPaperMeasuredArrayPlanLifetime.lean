import Blotto.GeneralPaperMeasuredFlattenLifetime

/-! Complete actual indexed-array size measurement. Child windows and
size lists are summed additively; the indexed prefix buffer, all callback
and loop frames, flattening, header arithmetic and final join coexist.
The theorem is compositional in actual child lifetimes, not runtime oracles. -/
namespace Blotto.GeneralPaperMeasuredArrayPlanLifetime
open GeneralPaperMeasuredBlockPlan (Plan references)
open GeneralPaperMeasuredPlanLifetimeAlgebra
open GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (arrayFootprint)
open GeneralPaperPayloadInstallationLifetime (cap)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

def callback {α : Type*} {n : ℕ} (S : ℕ) (measure : α → Plan) (source : FixedArrayTable n α) (j : Fin n) : List ℕ × ℕ :=
  ((measure (source.read j)).sizes,(measure (source.read j)).work + 32 * S + 32)

def measured {α : Type*} {n : ℕ} (S : ℕ) (measure : α → Plan) (source : FixedArrayTable n α) : FixedArrayTable n (List ℕ) × ℕ :=
  PaperIndexedArrayConstruction.run id S (callback S measure source)

theorem measured_data {α : Type*} {n : ℕ} (S : ℕ) (measure : α → Plan) (source : FixedArrayTable n α) :
    (measured S measure source).1.data.toList = List.ofFn (fun j : Fin n => (measure (source.read j)).sizes) := by
  simp only [measured,callback,PaperIndexedArrayConstruction.run_data,FixedArrayTable.ofFn,Array.toList_ofFn]

def payloadPlan {α : Type*} {n : ℕ} (S : ℕ) (measure : α → Plan) (source : FixedArrayTable n α) : Plan :=
  let actual := measured S measure source
  let flattened := GeneralPaperMeasuredArrayBlockPlan.flatten S actual.1.data.toList
  ⟨flattened.1,actual.2 + flattened.2 + 64 * S + 64⟩

theorem payload_sum {α : Type*} {n : ℕ} (S : ℕ) (measure : α → Plan) (source : FixedArrayTable n α) :
    (payloadPlan S measure source).sizes.sum = ∑ j : Fin n,(measure (source.read j)).sizes.sum := by
  simp only [payloadPlan,GeneralPaperMeasuredArrayBlockPlan.flatten_sum,measured_data,List.map_ofFn,List.sum_ofFn,Function.comp_def]

theorem array_eq {α : Type*} {n : ℕ} (model : RationalCostModel) (S A : ℕ) (measure : α → Plan) (source : FixedArrayTable n α) :
    GeneralPaperMeasuredArrayBlockPlan.array model S A measure source =
      GeneralPaperMeasuredBlockPlan.join S (references model S A n 1 64) (payloadPlan S measure source) := by
  simp only [GeneralPaperMeasuredArrayBlockPlan.array,payloadPlan,measured,source.size]
  rfl

def controls {α : Type*} {n : ℕ} (model : RationalCostModel) (S A : ℕ) (measure : α → Plan) (source : FixedArrayTable n α) : List ℕ :=
  let actual := measured S measure source
  let flattened := GeneralPaperMeasuredArrayBlockPlan.flatten S actual.1.data.toList
  [S,A,n,actual.2,flattened.2,actual.2+flattened.2,(payloadPlan S measure source).work,
    (GeneralPaperMeasuredArrayBlockPlan.array model S A measure source).work]

def window {α : Type*} {n : ℕ} (model : RationalCostModel) (S A : ℕ) (measure : α → Plan)
    (space : α → ℕ) (source : FixedArrayTable n α) : ℕ :=
  (∑ j : Fin n,space (source.read j)) + (∑ j : Fin n,GeneralPaperMeasuredLayoutStorage.planFoot S (measure (source.read j))) +
    arrayFootprint S (listFootprint S natBits) (measured S measure source).1 +
    GeneralPaperMeasuredIndexedArrayLifetime.frames S (callback S measure source) +
    GeneralPaperMeasuredFlattenLifetime.window S A (measured S measure source).1.data.toList +
    GeneralPaperMeasuredLayoutStorage.planFoot S (payloadPlan S measure source) + fields S (controls model S A measure source) + 128 * S +
    joinWindow S A (references model S A n 1 64) (payloadPlan S measure source)
      (GeneralPaperMeasuredScalarPlanLifetime.referencesWindow model S A n 1 64) 0

theorem good {α : Type*} {n : ℕ} (model : RationalCostModel) (S A C : ℕ) (measure : α → Plan)
    (space : α → ℕ) (source : FixedArrayTable n α) (hA : 0 < A)
    (hGood : ∀ j,Good model S A C (measure (source.read j)) (space (source.read j))) :
    Good model S A (C + 32) (GeneralPaperMeasuredArrayBlockPlan.array model S A measure source) (window model S A measure space source) := by
  have hPositive := GeneralPaperMeasuredPlanPositive.array model S A measure source hA (fun j => (hGood j).1)
  refine ⟨hPositive,?_⟩
  intro Q hCap hWork
  have hOriginalCap := hCap
  have hWhole := hWork
  rw [array_eq] at hWork
  change (references model S A n 1 64).work + (payloadPlan S measure source).work +
    (GeneralPaperMeasuredBlockPlan.append S (references model S A n 1 64).sizes (payloadPlan S measure source).sizes).2 + 64 * S + 64 ≤ Q at hWork
  have hPayloadWork : (payloadPlan S measure source).work ≤ Q := by omega
  have hMeasuredWork : (measured S measure source).2 ≤ Q := by
    dsimp only [payloadPlan] at hWork
    omega
  have hFlattenWork : (GeneralPaperMeasuredArrayBlockPlan.flatten S (measured S measure source).1.data.toList).2 ≤ Q := by
    dsimp only [payloadPlan] at hWork
    omega
  rw [GeneralPaperMeasuredArrayPlanWork.area] at hCap ⊢
  let P := ∑ j : Fin n,(measure (source.read j)).sizes.sum
  have hArea : A * (n + 64) + P < 2 ^ A := hCap
  have hN : n ≤ A * (n + 64) := by have h := Nat.mul_le_mul_right (n + 64) hA; nlinarith only [h]
  have hCount := binaryWordWidth_le_of_lt_pow hA (show n < 2 ^ A by omega)
  have hNext := GeneralPaperRayOperandWidthEnvelope.word_add n 1
  have hOne : binaryWordWidth 1 = 1 := by decide
  have hWidth : binaryWordWidth (n + 1) ≤ A + 8 := by omega
  have hChildCap : ∀ j,(measure (source.read j)).sizes.sum < 2 ^ A := by
    intro j
    have h := Finset.single_le_sum (f := fun i : Fin n => (measure (source.read i)).sizes.sum)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    change (measure (source.read j)).sizes.sum ≤ P at h
    omega
  have hChildWork : ∀ j,(measure (source.read j)).work ≤ Q := by
    intro j
    have h := Finset.single_le_sum (f := fun i : Fin n => (callback S measure source i).2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hRun := PaperIndexedArrayConstruction.run_work id S (callback S measure source)
    change (measured S measure source).2 = _ at hRun
    dsimp only [callback] at h hRun
    omega
  have hChildren : (∑ j : Fin n,space (source.read j)) ≤ (P + n) * C * unit model S A Q := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => (hGood j).2 Q (hChildCap j) (hChildWork j))
    have he : (∑ j : Fin n,((measure (source.read j)).sizes.sum + 1) * C * unit model S A Q) = (P + n) * C * unit model S A Q := by
      have he : (∑ j : Fin n,((measure (source.read j)).sizes.sum + 1) * C * unit model S A Q) =
          (∑ j : Fin n,((measure (source.read j)).sizes.sum + 1)) * C * unit model S A Q := by
        rw [Finset.sum_mul,Finset.sum_mul]
      rw [he,Finset.sum_add_distrib]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.mul_one]
      rfl
    exact h.trans_eq he
  have hPlans : (∑ j : Fin n,GeneralPaperMeasuredLayoutStorage.planFoot S (measure (source.read j))) ≤ (P + n) * unit model S A Q := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => plan_bound model S A Q _ (hGood j).1 hA (hChildCap j) (hChildWork j))
    have he : (∑ j : Fin n,((measure (source.read j)).sizes.sum + 1) * unit model S A Q) = (P + n) * unit model S A Q := by
      have he : (∑ j : Fin n,((measure (source.read j)).sizes.sum + 1) * unit model S A Q) =
          (∑ j : Fin n,((measure (source.read j)).sizes.sum + 1)) * unit model S A Q := by rw [Finset.sum_mul]
      rw [he,Finset.sum_add_distrib]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.mul_one]
      rfl
    exact h.trans_eq he
  have hLists : (∑ j : Fin n,listFootprint S natBits (measure (source.read j)).sizes) ≤ (P + n) * unit model S A Q := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => GeneralPaperMeasuredFlattenLifetime.size_list_bound model S A Q
      (measure (source.read j)).sizes hA (hGood j).1 (hChildCap j))
    have he : (∑ j : Fin n,((measure (source.read j)).sizes.sum + 1) * unit model S A Q) = (P + n) * unit model S A Q := by
      have he : (∑ j : Fin n,((measure (source.read j)).sizes.sum + 1) * unit model S A Q) =
          (∑ j : Fin n,((measure (source.read j)).sizes.sum + 1)) * unit model S A Q := by rw [Finset.sum_mul]
      rw [he,Finset.sum_add_distrib]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.mul_one]
      rfl
    exact h.trans_eq he
  have hUnit := unit_bounds model S A Q
  have hBuffer : arrayFootprint S (listFootprint S natBits) (measured S measure source).1 ≤ (P + n + 1) * 2 * unit model S A Q := by
    have hControl : S + 64 * S ≤ unit model S A Q := by omega
    have hPay := Nat.mul_le_mul_left (n + 1) hControl
    have hFactor := Nat.mul_le_mul_right (unit model S A Q) (show n + 1 ≤ P + n + 1 by omega)
    simp only [measured,PaperIndexedArrayConstruction.run_data,callback,arrayFootprint,FixedArrayTable.read_ofFn,
      Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    nlinarith only [hLists,hPay,hFactor]
  have hFrames := GeneralPaperMeasuredIndexedArrayLifetime.frames_bound model S A Q (callback S measure source) hWidth hMeasuredWork
  have hListPositive : ∀ xs ∈ (measured S measure source).1.data.toList,∀ x ∈ xs,0 < x := by
    rw [measured_data]
    intro xs hxs
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hxs
    exact (hGood j).1
  have hListSum : ((measured S measure source).1.data.toList.map List.sum).sum = P := by
    rw [measured_data]
    simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def]
    rfl
  have hFlat := GeneralPaperMeasuredFlattenLifetime.window_bound model S A Q (measured S measure source).1.data.toList hA hListPositive
    (by rw [hListSum]; omega) hFlattenWork
  have hLength : (measured S measure source).1.data.toList.length = n := by rw [measured_data,List.length_ofFn]
  rw [hListSum,hLength] at hFlat
  have hPayloadPos : GeneralPaperMeasuredPlanPositive.Positive (payloadPlan S measure source) := by
    intro x hx
    change x ∈ (GeneralPaperMeasuredArrayBlockPlan.flatten S (measured S measure source).1.data.toList).1 at hx
    rw [GeneralPaperMeasuredArrayBlockPlan.flatten_data] at hx
    obtain ⟨xs,hxs,hx⟩ := List.mem_flatten.mp hx
    exact hListPositive xs hxs x hx
  have hPayloadCap : (payloadPlan S measure source).sizes.sum < 2 ^ A := by rw [payload_sum]; change P < 2 ^ A; omega
  have hPayload := plan_bound model S A Q _ hPayloadPos hA hPayloadCap (by omega)
  rw [payload_sum] at hPayload
  have hHeader := GeneralPaperMeasuredScalarPlanLifetime.references_good model S A n 1 64 hA
    (Nat.mul_pos hA (by omega)) (by omega) (by change 1 ≤ A + 8; omega) (by change 7 ≤ A + 8; omega)
  have hHeaderSpace := hHeader.2 Q (by
    rw [GeneralPaperMeasuredBlockPlan.references_data]; simp only [Nat.one_mul,List.sum_cons,List.sum_nil,Nat.add_zero]; omega) (by omega)
  simp only [GeneralPaperMeasuredBlockPlan.references_data,Nat.one_mul,List.sum_cons,List.sum_nil,Nat.add_zero] at hHeaderSpace
  have hJoinCap : (GeneralPaperMeasuredBlockPlan.join S (references model S A n 1 64) (payloadPlan S measure source)).sizes.sum < 2 ^ A := by
    rw [← array_eq model S A measure source]
    exact hOriginalCap
  have hJoinWork : (GeneralPaperMeasuredBlockPlan.join S (references model S A n 1 64) (payloadPlan S measure source)).work ≤ Q := by
    rw [← array_eq model S A measure source]
    exact hWhole
  have hJoin := GeneralPaperMeasuredRecordPlanLifetime.join_overhead model S A Q
    (references model S A n 1 64) (payloadPlan S measure source) hA hHeader.1 hPayloadPos hJoinCap hJoinWork
  rw [GeneralPaperMeasuredBlockPlan.join_sum,GeneralPaperMeasuredBlockPlan.references_data,payload_sum] at hJoin
  simp only [Nat.one_mul,List.sum_cons,List.sum_nil,Nat.add_zero] at hJoin
  have hFields := fields_bound S (A + 9 + natBits (cap S A Q)) (controls model S A measure source) (by
    intro x hx
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|hx
    · have h := Nat.add_le_add_left (binaryWordWidth_mono (show x ≤ cap x A Q by unfold cap; omega)) 1
      change natBits x ≤ natBits (cap x A Q) at h; omega
    · have h := Nat.add_le_add_left (binaryWordWidth_mono (show x ≤ cap S x Q by unfold cap; omega)) 1
      change natBits x ≤ natBits (cap S x Q) at h; omega
    · unfold natBits; omega
    · have hp : x ≤ Q := by
        rcases hx with rfl|rfl|rfl|rfl|rfl
        · exact hMeasuredWork
        · exact hFlattenWork
        · dsimp only [payloadPlan] at hPayloadWork
          omega
        · exact hPayloadWork
        · exact hWhole
      have h := price_word S A Q x hp; omega)
  change fields S _ ≤ 8 * (A + 9 + natBits (cap S A Q) + S) + 32 * S at hFields
  have hParent : fields S (controls model S A measure source) + 128 * S ≤ unit model S A Q := by omega
  have hC := Nat.mul_le_mul_right (C * unit model S A Q) (show P + n ≤ A * (n + 64) + P + 1 by omega)
  have hP := Nat.mul_le_mul_right (unit model S A Q) (show P + n + 1 ≤ A * (n + 64) + P + 1 by omega)
  have hNPay := Nat.mul_le_mul_right (unit model S A Q) (show n + 1 ≤ A * (n + 64) + P + 1 by omega)
  have hHeaderPay := Nat.mul_le_mul_right (unit model S A Q) (show A * (n + 64) + 1 ≤ A * (n + 64) + P + 1 by omega)
  have hBase := Nat.mul_le_mul_right (unit model S A Q) (show 1 ≤ A * (n + 64) + P + 1 by omega)
  unfold window
  rw [GeneralPaperMeasuredRecordPlanLifetime.join_window_split]
  dsimp only [P] at hChildren hPlans hLists hBuffer hFlat hPayload hC hP hNPay hHeaderPay hBase
  nlinarith only [hChildren,hPlans,hBuffer,hFrames,hFlat,hPayload,hHeaderSpace,hJoin,hParent,hC,hP,hNPay,hHeaderPay,hBase]

end Blotto.GeneralPaperMeasuredArrayPlanLifetime
