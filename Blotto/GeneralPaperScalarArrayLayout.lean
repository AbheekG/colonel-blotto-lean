import Blotto.GeneralPaperPayloadMemory
import Blotto.GeneralPaperRowPrefix

/-! Scalar-array payload roots come from the executed measured layout.
The source array is traversed in its stored order. Each scalar has one
measured block, and the returned raw roots have exactly the source length
and distinct encoded values under the measured capacity. -/
namespace Blotto.GeneralPaperScalarArrayLayout
open GeneralPaperMeasuredBlockPlan GeneralPaperSequentialLayout
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

theorem flatten_singletons {α β : Type*} (f : α → β) (xs : List α) :
    (xs.map (fun x => [f x])).flatten = xs.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.flatten_cons,List.singleton_append,ih]

def plan {α : Type*} {n : ℕ} (model : RationalCostModel) (S A : ℕ) (measure : α → Plan)
    (source : FixedArrayTable n α) : Plan := GeneralPaperMeasuredArrayBlockPlan.array model S A measure source

theorem plan_data {α : Type*} {n : ℕ} (model : RationalCostModel) (S A : ℕ) (measure : α → Plan)
    (encode : α → ℕ) (source : FixedArrayTable n α) (hMeasure : ∀ x,(measure x).sizes = [encode x]) :
    (plan model S A measure source).sizes = A * (n + 64) :: source.data.toList.map encode := by
  rw [plan,GeneralPaperMeasuredArrayBlockPlan.array_data]
  simp_rw [hMeasure]
  rw [← GeneralPaperRowPrefix.list_ofFn source,List.map_ofFn]
  have h := flatten_singletons encode source.data.toList
  rw [← GeneralPaperRowPrefix.list_ofFn source,List.map_ofFn] at h
  simpa only [List.map_ofFn,Function.comp_def,List.singleton_append] using congrArg (fun xs => [A * (n + 64)] ++ xs) h

def payloads {α : Type*} {n : ℕ} (model : RationalCostModel) (S A base : ℕ) (measure : α → Plan)
    (source : FixedArrayTable n α) : List (Region A) :=
  (GeneralPaperMeasuredBlockLayout.run model S A base (plan model S A measure source)).1.tail

theorem payload_data {α : Type*} {n : ℕ} (model : RationalCostModel) (S A base : ℕ) (measure : α → Plan)
    (encode : α → ℕ) (source : FixedArrayTable n α) (hMeasure : ∀ x,(measure x).sizes = [encode x]) :
    payloads model S A base measure source =
      (GeneralPaperSequentialLayout.run model S A (base + A * (n + 64)) (source.data.toList.map encode)).1 := by
  unfold payloads GeneralPaperMeasuredBlockLayout.run
  rw [plan_data model S A measure encode source hMeasure]
  rfl

theorem payload_lengths {α : Type*} {n : ℕ} (model : RationalCostModel) (S A base : ℕ) (measure : α → Plan)
    (encode : α → ℕ) (source : FixedArrayTable n α) (hMeasure : ∀ x,(measure x).sizes = [encode x]) :
    (payloads model S A base measure source).map Region.length = source.data.toList.map encode := by
  rw [payload_data model S A base measure encode source hMeasure]
  exact GeneralPaperSequentialLayout.lengths model S A _ _

theorem payload_count {α : Type*} {n : ℕ} (model : RationalCostModel) (S A base : ℕ) (measure : α → Plan)
    (encode : α → ℕ) (source : FixedArrayTable n α) (hMeasure : ∀ x,(measure x).sizes = [encode x]) :
    (payloads model S A base measure source).length = n := by
  have h := congrArg List.length (payload_lengths model S A base measure encode source hMeasure)
  simpa only [List.length_map,Array.length_toList,source.size] using h

theorem payload_keys {α : Type*} {n : ℕ} (model : RationalCostModel) (S A base : ℕ) (measure : α → Plan)
    (encode : α → ℕ) (source : FixedArrayTable n α) (hMeasure : ∀ x,(measure x).sizes = [encode x])
    (hPositive : ∀ x,0 < encode x) (hCap : base + (plan model S A measure source).sizes.sum < 2 ^ A) :
    ((payloads model S A base measure source).map (fun r => r.reference.value)).Nodup := by
  have hData := plan_data model S A measure encode source hMeasure
  rw [hData,List.sum_cons] at hCap
  rw [payload_data model S A base measure encode source hMeasure]
  apply GeneralPaperMeasuredLayoutDistinct.reference_values model S A (base + A * (n + 64))
    (⟨source.data.toList.map encode,0⟩ : Plan)
  · intro size hSize
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hSize
    exact hPositive x
  · change base + A * (n + 64) + (source.data.toList.map encode).sum < 2 ^ A
    omega

theorem payload_range {α : Type*} {n : ℕ} (model : RationalCostModel) (S A base : ℕ) (measure : α → Plan)
    (encode : α → ℕ) (source : FixedArrayTable n α) (hMeasure : ∀ x,(measure x).sizes = [encode x]) :
    ∀ r ∈ payloads model S A base measure source,
      base + A * (n + 64) ≤ r.start ∧ r.stop ≤ base + (plan model S A measure source).sizes.sum := by
  rw [payload_data model S A base measure encode source hMeasure]
  intro r hr
  have h := GeneralPaperSequentialLayout.range model S A (base + A * (n + 64)) (source.data.toList.map encode) r hr
  rw [plan_data model S A measure encode source hMeasure,List.sum_cons]
  simpa only [Nat.add_assoc] using h

end Blotto.GeneralPaperScalarArrayLayout
