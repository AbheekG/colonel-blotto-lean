import Blotto.GeneralPaperMeasuredBlockPlan

/-! Measured indexed arrays of block plans. Each source payload measurer is
called once. Flattening copies the resulting short size words, not payloads;
the destination reference/header block is constructed by priced arithmetic. -/
namespace Blotto.GeneralPaperMeasuredArrayBlockPlan
open GeneralPaperMeasuredBlockPlan GeneralPaperEncodedBasisStorage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def flatten (S : ℕ) : List (List ℕ) → List ℕ × ℕ
  | [] => ([],64 * S + 64)
  | xs :: xss =>
    let later := flatten S xss
    let actual := GeneralPaperMeasuredBlockPlan.append S xs later.1
    (actual.1,later.2 + actual.2 + 64 * S + 64)

theorem flatten_data (S : ℕ) (xss : List (List ℕ)) : (flatten S xss).1 = xss.flatten := by
  induction xss with
  | nil => rfl
  | cons xs xss ih => simp only [flatten,append_data,ih,List.flatten_cons]

theorem flatten_sum (S : ℕ) (xss : List (List ℕ)) :
    (flatten S xss).1.sum = (xss.map List.sum).sum := by
  induction xss with
  | nil => rfl
  | cons xs xss ih => simp only [flatten,append_data,List.sum_append,ih,List.map_cons,List.sum_cons]

def array {α : Type*} {n : ℕ} (model : RationalCostModel) (S A : ℕ) (measure : α → Plan)
    (source : FixedArrayTable n α) : Plan :=
  let measured := PaperIndexedArrayConstruction.run id S (fun j : Fin n =>
    let actual := measure (source.read j)
    (actual.sizes,actual.work + 32 * S + 32))
  let flattened := flatten S measured.1.data.toList
  let payloads : Plan := ⟨flattened.1,measured.2 + flattened.2 + 64 * S + 64⟩
  let header := references model S A source.data.size 1 64
  join S header payloads

theorem array_data {α : Type*} {n : ℕ} (model : RationalCostModel) (S A : ℕ) (measure : α → Plan)
    (source : FixedArrayTable n α) :
    (array model S A measure source).sizes =
      [A * (n + 64)] ++ (List.ofFn (fun j : Fin n => (measure (source.read j)).sizes)).flatten := by
  simp only [array,join_data,references_data,flatten_data,PaperIndexedArrayConstruction.run_data,
    FixedArrayTable.ofFn,Array.toList_ofFn,source.size,one_mul]

theorem array_sum {α : Type*} {n : ℕ} (model : RationalCostModel) (S A : ℕ) (measure : α → Plan)
    (encode : α → ℕ) (source : FixedArrayTable n α)
    (h : ∀ j,(measure (source.read j)).sizes.sum = encode (source.read j)) :
    (array model S A measure source).sizes.sum = arrayFootprint A encode source := by
  have hFlat := flatten_sum S (List.ofFn (fun j : Fin n => (measure (source.read j)).sizes))
  rw [flatten_data] at hFlat
  rw [array_data,List.sum_append,hFlat]
  simp only [List.sum_cons,List.sum_nil,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  simp_rw [h]
  unfold arrayFootprint
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  ring

theorem array_blocks {α : Type*} {n : ℕ} (model : RationalCostModel) (S A : ℕ) (measure : α → Plan)
    (source : FixedArrayTable n α) :
    (array model S A measure source).sizes.length =
      1 + (List.ofFn (fun j : Fin n => (measure (source.read j)).sizes)).flatten.length := by
  rw [array_data,List.length_append]
  rfl

end Blotto.GeneralPaperMeasuredArrayBlockPlan
