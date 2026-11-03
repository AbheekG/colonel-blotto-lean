import Blotto.GeneralPaperPreparationResidentStorage

/-! Literal input/output lists and the structural selected-branch stack of
the native stable merge. Comparator scratch is its actual returned price;
the caller derives the uniform comparison bound from operand widths. This
is an erased reservation and stores no trace or length census. -/
namespace Blotto.GeneralPaperMergeConstructionStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def peak {α : Type*} (W : ℕ) (encode : α → ℕ) (compare : α → α → Bool × ℕ) : List α → List α → ℕ
  | [],_ => 64*W
  | _,[] => 64*W
  | x::xs,y::ys =>
    encode x+encode y+(compare x y).2+64*W+
      if (compare x y).1 then peak W encode compare xs (y::ys) else peak W encode compare (x::xs) ys
termination_by xs ys => xs.length+ys.length

theorem bounded {α : Type*} (W P C : ℕ) (encode : α → ℕ) (compare : α → α → Bool × ℕ) (xs ys : List α)
    (hx : ∀ x∈xs,encode x≤P) (hy : ∀ y∈ys,encode y≤P)
    (hc : ∀ x∈xs,∀ y∈ys,(compare x y).2≤C) :
    peak W encode compare xs ys≤(xs.length+ys.length)*(2*P+C+64*W)+64*W := by
  generalize hn : xs.length+ys.length=n
  induction n using Nat.strong_induction_on generalizing xs ys with
  | h n ih =>
    cases xs with
    | nil => simp only [peak]; omega
    | cons x xs =>
      cases ys with
      | nil => simp only [peak]; omega
      | cons y ys =>
        have ha := hx x (List.mem_cons_self ..)
        have hb := hy y (List.mem_cons_self ..)
        have hp := hc x (List.mem_cons_self ..) y (List.mem_cons_self ..)
        rw [peak]
        split
        · have hi := ih (xs.length+(y::ys).length) (by simp only [List.length_cons] at hn ⊢; omega)
            xs (y::ys) (fun a ha => hx a (List.mem_cons_of_mem _ ha)) hy
            (fun a ha b hb => hc a (List.mem_cons_of_mem _ ha) b hb) rfl
          simp only [List.length_cons] at hi hn ⊢
          nlinarith only [ha,hb,hp,hi,hn]
        · have hi := ih ((x::xs).length+ys.length) (by simp only [List.length_cons] at hn ⊢; omega)
            (x::xs) ys hx (fun b hb => hy b (List.mem_cons_of_mem _ hb))
            (fun a ha b hb => hc a ha b (List.mem_cons_of_mem _ hb)) rfl
          simp only [List.length_cons] at hi hn ⊢
          nlinarith only [ha,hb,hp,hi,hn]

theorem output {α : Type*} (W P : ℕ) (encode : α → ℕ) (compare : α → α → Bool × ℕ) (xs ys : List α)
    (hx : ∀ x∈xs,encode x≤P) (hy : ∀ y∈ys,encode y≤P) :
    listFootprint W encode (GeneralPaperPricedMerge.run compare W xs ys).1≤
      (xs.length+ys.length)*(P+2*W)+32*W := by
  apply (list_bound W P encode _ ?_).trans_eq
  · rw [GeneralPaperPricedMerge.length]
  · intro a ha
    rw [GeneralPaperPricedMerge.data] at ha
    have hp : (List.merge xs ys (fun a b => (compare a b).1)).Perm (xs++ys) := List.merge_perm_append _
    rcases List.mem_append.mp (hp.mem_iff.mp ha) with ha|ha
    · exact hx a ha
    · exact hy a ha

def window {α : Type*} (W : ℕ) (encode : α → ℕ) (compare : α → α → Bool × ℕ) (xs ys : List α) : ℕ :=
  listFootprint W encode xs+listFootprint W encode ys+
    listFootprint W encode (GeneralPaperPricedMerge.run compare W xs ys).1+peak W encode compare xs ys

theorem whole {α : Type*} (W P C : ℕ) (encode : α → ℕ) (compare : α → α → Bool × ℕ) (xs ys : List α)
    (hx : ∀ x∈xs,encode x≤P) (hy : ∀ y∈ys,encode y≤P)
    (hc : ∀ x∈xs,∀ y∈ys,(compare x y).2≤C) :
    window W encode compare xs ys≤(xs.length+ys.length)*(4*P+C+68*W)+160*W := by
  have a := list_bound W P encode xs hx
  have b := list_bound W P encode ys hy
  have c := output W P encode compare xs ys hx hy
  have d := bounded W P C encode compare xs ys hx hy hc
  exact (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add a b) c) d).trans_eq (by ring)

end Blotto.GeneralPaperMergeConstructionStorage
