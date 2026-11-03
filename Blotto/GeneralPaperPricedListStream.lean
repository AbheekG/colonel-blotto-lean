import Blotto.GeneralPaperAffineCrossingPrice

/-! Sequential list filterMap/flatMap with explicit source reference and
append costs. Each callback is invoked once per visited element; append
copies only the current output segment, never an accumulated prefix.
-/
namespace Blotto.GeneralPaperPricedListStream
set_option autoImplicit false
set_option maxHeartbeats 2500000

def filterMap {α β : Type*} (W : ℕ) (evaluate : α → Option β × ℕ) : List α → List β × ℕ
  | [] => ([],2*W)
  | a::rest =>
    let current := evaluate a
    let later := filterMap W evaluate rest
    (match current.1 with | none => later.1 | some b => b::later.1,current.2+later.2+8*W)

theorem filterMap_data {α β : Type*} (W : ℕ) (evaluate : α → Option β × ℕ) (xs : List α) :
    (filterMap W evaluate xs).1=xs.filterMap (fun a => (evaluate a).1) := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    rw [filterMap,List.filterMap_cons]
    cases (evaluate a).1 <;> simp only [ih]

theorem filterMap_length {α β : Type*} (W : ℕ) (evaluate : α → Option β × ℕ) (xs : List α) :
    (filterMap W evaluate xs).1.length≤xs.length := by
  rw [filterMap_data]
  exact List.length_filterMap_le _ _

theorem filterMap_work {α β : Type*} (W C : ℕ) (evaluate : α → Option β × ℕ) (xs : List α)
    (h : ∀ a∈xs,(evaluate a).2≤C) :
    (filterMap W evaluate xs).2≤(C+8*W)*xs.length+2*W := by
  induction xs with
  | nil => simp only [filterMap,List.length_nil,Nat.mul_zero,Nat.zero_add,le_refl]
  | cons a rest ih =>
    have hr := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a List.mem_cons_self
    change (evaluate a).2+(filterMap W evaluate rest).2+8*W≤_
    simp only [List.length_cons]
    nlinarith only [hr,ha]

def flatMap {α β : Type*} (W : ℕ) (evaluate : α → List β × ℕ) : List α → List β × ℕ
  | [] => ([],2*W)
  | a::rest =>
    let current := evaluate a
    let appendCost := (8*current.1.length+8)*W
    let later := flatMap W evaluate rest
    (current.1++later.1,current.2+later.2+appendCost)

theorem flatMap_data {α β : Type*} (W : ℕ) (evaluate : α → List β × ℕ) (xs : List α) :
    (flatMap W evaluate xs).1=xs.flatMap (fun a => (evaluate a).1) := by
  induction xs with
  | nil => rfl
  | cons a rest ih => simp only [flatMap,List.flatMap_cons,ih]

theorem flatMap_length {α β : Type*} (W B : ℕ) (evaluate : α → List β × ℕ) (xs : List α)
    (h : ∀ a∈xs,(evaluate a).1.length≤B) : (flatMap W evaluate xs).1.length≤xs.length*B := by
  induction xs with
  | nil => simp only [flatMap,List.length_nil,Nat.zero_mul,le_refl]
  | cons a rest ih =>
    have hr := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a List.mem_cons_self
    change ((evaluate a).1++(flatMap W evaluate rest).1).length≤_
    rw [List.length_append]
    simp only [List.length_cons]
    nlinarith only [hr,ha]

theorem flatMap_work {α β : Type*} (W B C : ℕ) (evaluate : α → List β × ℕ) (xs : List α)
    (hLength : ∀ a∈xs,(evaluate a).1.length≤B) (hWork : ∀ a∈xs,(evaluate a).2≤C) :
    (flatMap W evaluate xs).2≤(C+(8*B+8)*W)*xs.length+2*W := by
  induction xs with
  | nil => simp only [flatMap,List.length_nil,Nat.mul_zero,Nat.zero_add,le_refl]
  | cons a rest ih =>
    have hr := ih (fun b hb => hLength b (List.mem_cons_of_mem _ hb)) (fun b hb => hWork b (List.mem_cons_of_mem _ hb))
    have hl := hLength a List.mem_cons_self
    have ha := hWork a List.mem_cons_self
    have hm := Nat.mul_le_mul_right W (Nat.add_le_add_right (Nat.mul_le_mul_left 8 hl) 8)
    change (evaluate a).2+(flatMap W evaluate rest).2+(8*(evaluate a).1.length+8)*W≤_
    simp only [List.length_cons]
    nlinarith only [hr,ha,hm]

end Blotto.GeneralPaperPricedListStream
