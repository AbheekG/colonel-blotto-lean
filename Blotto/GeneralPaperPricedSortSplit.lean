import Blotto.GeneralPaperPricedMerge

/-! Contiguous splitting for the priced stable sort. The cut is constructed
by the arithmetic bounded-quotient program, without a floor primitive.
The word price includes length, take/drop, references and loop control.
-/
namespace Blotto.GeneralPaperPricedSortSplit
set_option autoImplicit false

structure Result (α : Type*) where
  left : List α
  right : List α
  work : ℕ

def cut {α : Type*} (depth : ℕ) (xs : List α) : ℕ :=
  (GeneralPaperRankMidpoint.midpoint depth 0 (xs.length+1)).quotient

def run {α : Type*} (W depth : ℕ) (xs : List α) : Result α :=
  let middle := GeneralPaperRankMidpoint.midpoint depth 0 (xs.length+1)
  ⟨xs.take middle.quotient,xs.drop middle.quotient,
    (16*xs.length+24)*W+middle.work*W⟩

theorem append {α : Type*} (W depth : ℕ) (xs : List α) :
    (run W depth xs).left++(run W depth xs).right=xs :=
  List.take_append_drop _ _

theorem lengths {α : Type*} (W depth : ℕ) (xs : List α) :
    (run W depth xs).left.length+(run W depth xs).right.length=xs.length := by
  rw [←List.length_append,append]

theorem left_mem {α : Type*} (W depth : ℕ) (xs : List α) (a : α)
    (h : a∈(run W depth xs).left) : a∈xs :=
  List.mem_of_mem_take h

theorem right_mem {α : Type*} (W depth : ℕ) (xs : List α) (a : α)
    (h : a∈(run W depth xs).right) : a∈xs :=
  List.mem_of_mem_drop h

theorem cut_eq {α : Type*} (depth : ℕ) (xs : List α)
    (hSize : xs.length+1<2^depth) : cut depth xs=(xs.length+1)/2 := by
  have hm := GeneralPaperRankMidpoint.midpoint_bounds (xs.length+1) depth 0
    (xs.length+1) (by omega) le_rfl hSize
  dsimp only [cut]
  omega

theorem data {α : Type*} (W depth : ℕ) (xs : List α)
    (hSize : xs.length+1<2^depth) :
    (run W depth xs).left=xs.take ((xs.length+1)/2) ∧
    (run W depth xs).right=xs.drop ((xs.length+1)/2) := by
  have hc := cut_eq depth xs hSize
  change xs.take (cut depth xs)=_ ∧ xs.drop (cut depth xs)=_
  rw [hc]
  exact ⟨rfl,rfl⟩

theorem half_lengths {α : Type*} (W depth fuel : ℕ) (xs : List α)
    (hSize : xs.length+1<2^depth) (hFuel : xs.length≤2^(fuel+1)) :
    (run W depth xs).left.length≤2^fuel ∧
    (run W depth xs).right.length≤2^fuel := by
  have hd := data W depth xs hSize
  rw [hd.1,hd.2,List.length_take,List.length_drop]
  rw [pow_succ] at hFuel
  omega

theorem work {α : Type*} (W depth : ℕ) (xs : List α) :
    (run W depth xs).work=(16*xs.length+26+12*depth)*W := by
  simp only [run,GeneralPaperRankMidpoint.midpoint_work]
  ring

end Blotto.GeneralPaperPricedSortSplit
