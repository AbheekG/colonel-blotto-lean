import Blotto.GeneralPaperMeasuredArrayBlockPlan

/-! List and record-field plans traverse actual source lists, measuring each
payload once and computing the count through priced scalar increments. The
reference/header stride distinguishes linked cells from record fields. -/
namespace Blotto.GeneralPaperMeasuredListBlockPlan
open GeneralPaperMeasuredBlockPlan GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

structure Body where
  sizes : List ℕ
  count : ℕ
  work : ℕ

def body {α : Type*} (model : RationalCostModel) (S : ℕ) (measure : α → Plan) : List α → Body
  | [] => ⟨[],0,64 * S + 64⟩
  | x :: xs =>
    let current := measure x
    let later := body model S measure xs
    let actual := GeneralPaperMeasuredBlockPlan.append S current.sizes later.sizes
    let count := GeneralPaperNaturalScalarStep.run model S .add later.count 1
    ⟨actual.1,count.1,current.work + later.work + actual.2 + count.2 + 64 * S + 64⟩

theorem body_count {α : Type*} (model : RationalCostModel) (S : ℕ) (measure : α → Plan) (xs : List α) :
    (body model S measure xs).count = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [body,GeneralPaperNaturalScalarStep.run,GeneralPaperNaturalScalarStep.Op.apply,ih,List.length_cons]

theorem body_data {α : Type*} (model : RationalCostModel) (S : ℕ) (measure : α → Plan) (xs : List α) :
    (body model S measure xs).sizes = (xs.map (fun x => (measure x).sizes)).flatten := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [body,append_data,ih,List.map_cons,List.flatten_cons]

theorem body_sum {α : Type*} (model : RationalCostModel) (S : ℕ) (measure : α → Plan) (xs : List α) :
    (body model S measure xs).sizes.sum = (xs.map (fun x => (measure x).sizes.sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [body,append_data,List.sum_append,ih,List.map_cons,List.sum_cons]

def run {α : Type*} (model : RationalCostModel) (S A stride fixed : ℕ) (measure : α → Plan) (xs : List α) : Plan :=
  let actual := body model S measure xs
  let header := references model S A actual.count stride fixed
  join S header ⟨actual.sizes,actual.work⟩

theorem data {α : Type*} (model : RationalCostModel) (S A stride fixed : ℕ) (measure : α → Plan) (xs : List α) :
    (run model S A stride fixed measure xs).sizes =
      [A * (stride * xs.length + fixed)] ++ (xs.map (fun x => (measure x).sizes)).flatten := by
  simp only [run,join_data,references_data,body_count,body_data]

theorem sum {α : Type*} (model : RationalCostModel) (S A stride fixed : ℕ) (measure : α → Plan)
    (encode : α → ℕ) (xs : List α) (h : ∀ x ∈ xs,(measure x).sizes.sum = encode x) :
    (run model S A stride fixed measure xs).sizes.sum = A * (stride * xs.length + fixed) + (xs.map encode).sum := by
  dsimp only [run]
  rw [join_sum,references_data,body_count,body_sum]
  simp only [List.sum_cons,List.sum_nil,Nat.add_zero]
  congr 1
  apply congrArg List.sum
  exact List.map_congr_left h

theorem linked_sum {α : Type*} (model : RationalCostModel) (S A : ℕ) (measure : α → Plan)
    (encode : α → ℕ) (xs : List α) (h : ∀ x ∈ xs,(measure x).sizes.sum = encode x) :
    (run model S A 2 32 measure xs).sizes.sum = listFootprint A encode xs := by
  rw [sum model S A 2 32 measure encode xs h]
  unfold listFootprint
  ring

theorem fields_sum (model : RationalCostModel) (S A : ℕ) (xs : List ℕ) :
    (run model S A 1 32 (natural model S) xs).sizes.sum = fields A xs := by
  rw [sum model S A 1 32 (natural model S) natBits xs (by
    intro x _
    rw [natural_data]
    simp only [List.sum_cons,List.sum_nil,Nat.add_zero])]
  unfold fields
  ring

end Blotto.GeneralPaperMeasuredListBlockPlan
