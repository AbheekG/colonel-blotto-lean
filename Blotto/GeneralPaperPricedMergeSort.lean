import Blotto.GeneralPaperPricedSortSplit

/-! Stable merge sort with explicit comparator and reference/control prices.
Fuel is bounded by a constructed doubling depth; a short-fuel return is only
a totality fallback. Permutation and the work bound hold for every fuel.
-/
namespace Blotto.GeneralPaperPricedMergeSort
set_option autoImplicit false
set_option maxHeartbeats 4500000

def run {α : Type*} (compare : α → α → Bool × ℕ) (W depth : ℕ) :
    ℕ → List α → List α × ℕ
  | 0,xs => (xs,2*W)
  | _+1,[] => ([],2*W)
  | _+1,[a] => ([a],2*W)
  | fuel+1,a::b::rest =>
    let halves := GeneralPaperPricedSortSplit.run W depth (a::b::rest)
    let left := run compare W depth fuel halves.left
    let right := run compare W depth fuel halves.right
    let merged := GeneralPaperPricedMerge.run compare W left.1 right.1
    (merged.1,left.2+right.2+merged.2+halves.work+8*W)

theorem perm {α : Type*} (compare : α → α → Bool × ℕ) (W depth fuel : ℕ) (xs : List α) :
    (run compare W depth fuel xs).1.Perm xs := by
  induction fuel generalizing xs with
  | zero => exact List.Perm.refl _
  | succ fuel ih =>
    cases xs with
    | nil => exact List.Perm.refl _
    | cons a xs =>
      cases xs with
      | nil => exact List.Perm.refl _
      | cons b rest =>
        dsimp only [run]
        rw [GeneralPaperPricedMerge.data]
        exact (List.merge_perm_append _).trans
          (((ih _).append (ih _)).trans
            (List.Perm.of_eq (GeneralPaperPricedSortSplit.append W depth _)))

theorem length {α : Type*} (compare : α → α → Bool × ℕ) (W depth fuel : ℕ) (xs : List α) :
    (run compare W depth fuel xs).1.length=xs.length :=
  (perm compare W depth fuel xs).length_eq

theorem mem {α : Type*} (compare : α → α → Bool × ℕ) (W depth fuel : ℕ) (xs : List α) (a : α) :
    a∈(run compare W depth fuel xs).1 ↔ a∈xs :=
  (perm compare W depth fuel xs).mem_iff

theorem data {α : Type*} (compare : α → α → Bool × ℕ) (W depth fuel : ℕ) (xs : List α)
    (hSize : xs.length+1<2^depth) (hFuel : xs.length≤2^fuel) :
    (run compare W depth fuel xs).1=xs.mergeSort (fun a b => (compare a b).1) := by
  induction fuel generalizing xs with
  | zero =>
    simp only [pow_zero] at hFuel
    cases xs with
    | nil => simp only [run,List.mergeSort]
    | cons a xs =>
      cases xs with
      | nil => simp only [run,List.mergeSort]
      | cons b rest => simp only [List.length_cons] at hFuel; omega
  | succ fuel ih =>
    cases xs with
    | nil => simp only [run,List.mergeSort]
    | cons a xs =>
      cases xs with
      | nil => simp only [run,List.mergeSort]
      | cons b rest =>
        have hh := GeneralPaperPricedSortSplit.half_lengths W depth fuel (a::b::rest) hSize hFuel
        have hs := GeneralPaperPricedSortSplit.lengths W depth (a::b::rest)
        have hl := ih (GeneralPaperPricedSortSplit.run W depth (a::b::rest)).left (by omega) hh.1
        have hr := ih (GeneralPaperPricedSortSplit.run W depth (a::b::rest)).right (by omega) hh.2
        have hd := GeneralPaperPricedSortSplit.data W depth (a::b::rest) hSize
        dsimp only [run]
        rw [GeneralPaperPricedMerge.data,hl,hr,hd.1,hd.2]
        simp only [List.mergeSort,List.MergeSort.Internal.splitInTwo_fst,
          List.MergeSort.Internal.splitInTwo_snd]

theorem work {α : Type*} (compare : α → α → Bool × ℕ) (W depth fuel P : ℕ) (xs : List α)
    (h : ∀ a∈xs,∀ b∈xs,(compare a b).2≤P) :
    (run compare W depth fuel xs).2≤
      xs.length*(fuel+1)*(P+(128+24*depth)*W)+2*W := by
  induction fuel generalizing xs with
  | zero => simp only [run]; omega
  | succ fuel ih =>
    cases xs with
    | nil => simp only [run,List.length_nil,Nat.zero_mul,Nat.zero_add]
             exact le_rfl
    | cons a xs =>
      cases xs with
      | nil => simp only [run]; omega
      | cons b rest =>
        let halves := GeneralPaperPricedSortSplit.run W depth (a::b::rest)
        have hs : halves.left.length+halves.right.length=(a::b::rest).length :=
          GeneralPaperPricedSortSplit.lengths W depth _
        have hLeft (x : α) (hx : x∈halves.left) : x∈a::b::rest :=
          GeneralPaperPricedSortSplit.left_mem W depth _ x hx
        have hRight (x : α) (hx : x∈halves.right) : x∈a::b::rest :=
          GeneralPaperPricedSortSplit.right_mem W depth _ x hx
        have hl := ih halves.left (fun x hx y hy => h x (hLeft x hx) y (hLeft y hy))
        have hr := ih halves.right (fun x hx y hy => h x (hRight x hx) y (hRight y hy))
        have hm := GeneralPaperPricedMerge.work compare W P
          (run compare W depth fuel halves.left).1 (run compare W depth fuel halves.right).1
          (fun x hx y hy => h x (hLeft x ((mem compare W depth fuel halves.left x).mp hx))
            y (hRight y ((mem compare W depth fuel halves.right y).mp hy)))
        rw [length,length,hs] at hm
        have hp : halves.work=(16*(a::b::rest).length+26+12*depth)*W :=
          GeneralPaperPricedSortSplit.work W depth _
        have hn : 2≤(a::b::rest).length := by simp only [List.length_cons]; omega
        change (run compare W depth fuel halves.left).2+
          (run compare W depth fuel halves.right).2+
          (GeneralPaperPricedMerge.run compare W
            (run compare W depth fuel halves.left).1 (run compare W depth fuel halves.right).1).2+
          halves.work+8*W≤_
        have hsum := Nat.add_le_add hl hr
        have hfactor : halves.left.length*(fuel+1)*(P+(128+24*depth)*W)+
            halves.right.length*(fuel+1)*(P+(128+24*depth)*W)=
            (a::b::rest).length*(fuel+1)*(P+(128+24*depth)*W) := by
          rw [←Nat.add_mul,←Nat.add_mul,hs]
        have hslack := Nat.mul_le_mul_right ((32+12*depth)*W)
          (show 1≤(a::b::rest).length by omega)
        nlinarith only [hsum,hfactor,hm,hp,hs,hn,hslack,
          Nat.zero_le (W*depth),Nat.zero_le (W*(a::b::rest).length)]

end Blotto.GeneralPaperPricedMergeSort
