import Blotto.GeneralPaperSortConstructionStorage

/-! Structural clipping-map and adjacent-deduplication frames. Literal
current/last values are counted through the recursion; all returned lists
inherit the input value cap and native length bound. Primitive scratch is
joined by the enclosing complete order-construction allowance. -/
namespace Blotto.GeneralPaperNaturalListConstructionStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def clipPeak (W U : ℕ) : List ℕ → ℕ
  | [] => 64*W
  | x::rest => natBits x+natBits (min x U)+64*W+clipPeak W U rest

theorem clip_bound (W U : ℕ) (xs : List ℕ) (hx : ∀ x∈xs,x≤U) :
    clipPeak W U xs≤xs.length*(2*natBits U+64*W)+64*W := by
  induction xs with
  | nil => simp only [clipPeak,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons x rest ih =>
    have hX : natBits x≤natBits U := Nat.add_le_add_left (binaryWordWidth_mono (hx x (List.mem_cons_self ..))) 1
    have hMin : natBits (min x U)≤natBits U := Nat.add_le_add_left (binaryWordWidth_mono (Nat.min_le_right x U)) 1
    have hRest := ih (fun y hy => hx y (List.mem_cons_of_mem _ hy))
    change natBits x+natBits (min x U)+64*W+clipPeak W U rest≤(rest.length+1)*(2*natBits U+64*W)+64*W
    nlinarith only [hX,hMin,hRest]

def afterPeak (W : ℕ) : ℕ → List ℕ → ℕ
  | last,[] => natBits last+64*W
  | last,x::rest => natBits last+natBits x+64*W+
      if x=last then afterPeak W last rest else afterPeak W x rest

theorem after_bound (W U last : ℕ) (xs : List ℕ) (hl : last≤U) (hx : ∀ x∈xs,x≤U) :
    afterPeak W last xs≤xs.length*(2*natBits U+64*W)+natBits U+64*W := by
  induction xs generalizing last with
  | nil =>
    have h : natBits last≤natBits U := Nat.add_le_add_left (binaryWordWidth_mono hl) 1
    change natBits last+64*W≤0*(2*natBits U+64*W)+natBits U+64*W
    omega
  | cons x rest ih =>
    have hX := hx x (List.mem_cons_self ..)
    have hXW : natBits x≤natBits U := Nat.add_le_add_left (binaryWordWidth_mono hX) 1
    have hLW : natBits last≤natBits U := Nat.add_le_add_left (binaryWordWidth_mono hl) 1
    have hRest : ∀ y∈rest,y≤U := fun y hy => hx y (List.mem_cons_of_mem _ hy)
    rw [afterPeak]
    split
    · have hi := ih last hl hRest
      simp only [List.length_cons]
      nlinarith only [hi,hXW,hLW]
    · have hi := ih x hX hRest
      simp only [List.length_cons]
      nlinarith only [hi,hXW,hLW]

theorem after_properties (primitive : ℕ → ℕ) (W last : ℕ) (xs : List ℕ) :
    (GeneralPaperNaturalOrderPrice.after primitive W last xs).1.length≤xs.length ∧
      ∀ x∈(GeneralPaperNaturalOrderPrice.after primitive W last xs).1,x∈xs := by
  induction xs generalizing last with
  | nil => exact ⟨Nat.le_refl _,fun _ h => h⟩
  | cons x rest ih =>
    rw [GeneralPaperNaturalOrderPrice.after]
    dsimp only
    split
    · have h := ih last
      refine ⟨by simp only [List.length_cons]; omega,?_⟩
      intro y hy
      exact List.mem_cons_of_mem _ (h.2 y hy)
    · have h := ih x
      refine ⟨by simp only [List.length_cons]; omega,?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with hy|hy
      · exact List.mem_cons.mpr (Or.inl hy)
      · exact List.mem_cons_of_mem _ (h.2 y hy)

theorem unique_properties (primitive : ℕ → ℕ) (W : ℕ) (xs : List ℕ) :
    (GeneralPaperNaturalOrderPrice.unique primitive W xs).1.length≤xs.length ∧
      ∀ x∈(GeneralPaperNaturalOrderPrice.unique primitive W xs).1,x∈xs := by
  cases xs with
  | nil => exact ⟨Nat.le_refl _,fun _ h => h⟩
  | cons x rest =>
    have h := after_properties primitive W x rest
    refine ⟨Nat.add_le_add_right h.1 1,?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with hy|hy
    · exact List.mem_cons.mpr (Or.inl hy)
    · exact List.mem_cons_of_mem _ (h.2 y hy)

def uniquePeak (W : ℕ) : List ℕ → ℕ
  | [] => 64*W
  | x::rest => natBits x+64*W+afterPeak W x rest

theorem unique_bound (W U : ℕ) (xs : List ℕ) (hx : ∀ x∈xs,x≤U) :
    uniquePeak W xs≤xs.length*(2*natBits U+64*W)+natBits U+128*W := by
  cases xs with
  | nil => simp only [uniquePeak,List.length_nil]; omega
  | cons x rest =>
    have hX := hx x (List.mem_cons_self ..)
    have hWord : natBits x≤natBits U := Nat.add_le_add_left (binaryWordWidth_mono hX) 1
    have h := after_bound W U x rest hX (fun y hy => hx y (List.mem_cons_of_mem _ hy))
    change natBits x+64*W+afterPeak W x rest≤(rest.length+1)*(2*natBits U+64*W)+natBits U+128*W
    nlinarith only [h,hWord]

end Blotto.GeneralPaperNaturalListConstructionStorage
