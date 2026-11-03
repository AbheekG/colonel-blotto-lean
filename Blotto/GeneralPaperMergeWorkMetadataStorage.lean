import Blotto.GeneralPaperRankMidpointStorage
import Blotto.GeneralPaperSortConstructionStorage

/-! Encoded native stable-merge work metadata. Both possible child return
counters are conservatively bounded in a frame; only the selected child's
stack is retained. Existing list/payload/comparator windows are separate. -/
namespace Blotto.GeneralPaperMergeWorkMetadataStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

def workCap (W C N : ℕ) : ℕ := (C+8*W)*N+2*W
def metadataCap (W C N : ℕ) : ℕ := N+1+3*workCap W C N+C+8*W
def frameProfile (W C N : ℕ) : ℕ := 8*(natBits (metadataCap W C N)+W)+160*W

theorem work_bound {α : Type*} (compare : α → α → Bool×ℕ) (W C N : ℕ) (xs ys : List α)
    (hN : xs.length+ys.length≤N) (hc : ∀ a∈xs,∀ b∈ys,(compare a b).2≤C) :
    (GeneralPaperPricedMerge.run compare W xs ys).2≤workCap W C N :=
  (GeneralPaperPricedMerge.work compare W C xs ys hc).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ hN) _)

def frame {α : Type*} (compare : α → α → Bool×ℕ) (W : ℕ) (x y : α) (xs ys : List α) : ℕ :=
  let current := compare x y
  let left := GeneralPaperPricedMerge.run compare W xs (y::ys)
  let right := GeneralPaperPricedMerge.run compare W (x::xs) ys
  let result := GeneralPaperPricedMerge.run compare W (x::xs) (y::ys)
  fields W [(x::xs).length+(y::ys).length,result.2,current.2,left.2,right.2,left.2+current.2,right.2+current.2,8*W]+128*W

theorem frame_bound {α : Type*} (compare : α → α → Bool×ℕ) (W C N : ℕ) (x y : α) (xs ys : List α)
    (hN : (x::xs).length+(y::ys).length≤N) (hc : ∀ a∈x::xs,∀ b∈y::ys,(compare a b).2≤C) :
    frame compare W x y xs ys≤frameProfile W C N := by
  have hCurrent := hc x List.mem_cons_self y List.mem_cons_self
  have hResult := work_bound compare W C N (x::xs) (y::ys) hN hc
  have hLeft := work_bound compare W C N xs (y::ys) (by simp only [List.length_cons] at hN ⊢; omega)
    (fun a ha b hb => hc a (List.mem_cons_of_mem _ ha) b hb)
  have hRight := work_bound compare W C N (x::xs) ys (by simp only [List.length_cons] at hN ⊢; omega)
    (fun a ha b hb => hc a ha b (List.mem_cons_of_mem _ hb))
  have hf := fields_bound W (natBits (metadataCap W C N))
    [(x::xs).length+(y::ys).length,(GeneralPaperPricedMerge.run compare W (x::xs) (y::ys)).2,
      (compare x y).2,(GeneralPaperPricedMerge.run compare W xs (y::ys)).2,
      (GeneralPaperPricedMerge.run compare W (x::xs) ys).2,
      (GeneralPaperPricedMerge.run compare W xs (y::ys)).2+(compare x y).2,
      (GeneralPaperPricedMerge.run compare W (x::xs) ys).2+(compare x y).2,8*W] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤8*(natBits (metadataCap W C N)+W)+32*W at hf
  unfold frame frameProfile
  dsimp only
  omega

def peak {α : Type*} (compare : α → α → Bool×ℕ) (W : ℕ) : List α → List α → ℕ
  | [],ys => fields W [ys.length,(GeneralPaperPricedMerge.run compare W [] ys).2]+128*W
  | xs,[] => fields W [xs.length,(GeneralPaperPricedMerge.run compare W xs []).2]+128*W
  | x::xs,y::ys => frame compare W x y xs ys+
      if (compare x y).1 then peak compare W xs (y::ys) else peak compare W (x::xs) ys
termination_by xs ys => xs.length+ys.length

def profile (W C N : ℕ) : ℕ := (N+1)*frameProfile W C N

theorem bounded {α : Type*} (compare : α → α → Bool×ℕ) (W C N : ℕ) (xs ys : List α)
    (hN : xs.length+ys.length≤N) (hc : ∀ a∈xs,∀ b∈ys,(compare a b).2≤C) :
    peak compare W xs ys≤(xs.length+ys.length+1)*frameProfile W C N := by
  have base (n : ℕ) (hn : n≤N) : fields W [n,2*W]+128*W≤frameProfile W C N := by
    have hf := fields_bound W (natBits (metadataCap W C N)) [n,2*W] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl
      all_goals unfold metadataCap workCap; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤2*(natBits (metadataCap W C N)+W)+32*W at hf
    unfold frameProfile
    omega
  generalize hn : xs.length+ys.length=n
  induction n using Nat.strong_induction_on generalizing xs ys with
  | h n ih =>
    cases xs with
    | nil =>
      have hb := base ys.length (by simpa only [List.length_nil,Nat.zero_add] using hN)
      simp only [peak,GeneralPaperPricedMerge.run]
      exact hb.trans (Nat.le_mul_of_pos_left _ (by omega))
    | cons x xs =>
      cases ys with
      | nil =>
        have hb := base (x::xs).length (by simpa only [List.length_nil,Nat.add_zero] using hN)
        simp only [peak,GeneralPaperPricedMerge.run]
        exact hb.trans (Nat.le_mul_of_pos_left _ (by omega))
      | cons y ys =>
        have hf := frame_bound compare W C N x y xs ys hN hc
        rw [peak]
        split
        · have hi := ih (xs.length+(y::ys).length) (by simp only [List.length_cons] at hn ⊢; omega) xs (y::ys)
            (by simp only [List.length_cons] at hN ⊢; omega) (fun a ha b hb => hc a (List.mem_cons_of_mem _ ha) b hb) rfl
          have hAll := Nat.add_le_add hf hi
          exact hAll.trans_eq (by rw [←hn]; simp only [List.length_cons]; ring)
        · have hi := ih ((x::xs).length+ys.length) (by simp only [List.length_cons] at hn ⊢; omega) (x::xs) ys
            (by simp only [List.length_cons] at hN ⊢; omega) (fun a ha b hb => hc a ha b (List.mem_cons_of_mem _ hb)) rfl
          have hAll := Nat.add_le_add hf hi
          exact hAll.trans_eq (by rw [←hn]; simp only [List.length_cons]; ring)

theorem complete {α : Type*} (compare : α → α → Bool×ℕ) (W C N : ℕ) (xs ys : List α)
    (hN : xs.length+ys.length≤N) (hc : ∀ a∈xs,∀ b∈ys,(compare a b).2≤C) :
    peak compare W xs ys≤profile W C N :=
  (bounded compare W C N xs ys hN hc).trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hN 1))

end Blotto.GeneralPaperMergeWorkMetadataStorage
