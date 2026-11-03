import Blotto.GeneralPaperPricedSort
import Blotto.PlayerSpecificSweep

/-! A sharper work bound for the existing literal merge sort. Its split
midpoint costs the global depth once per internal node. Counting the full
binary recursion tree avoids charging that depth once per element/level. -/
namespace Blotto.PlayerSpecificSortWork
set_option autoImplicit false
set_option maxHeartbeats 4000000

def node (W depth : ℕ) : ℕ := (36+12*depth)*W

theorem tree_work {α : Type*} (compare : α → α → Bool×ℕ) (W depth fuel P : ℕ) (xs : List α)
    (h : ∀ a∈xs,∀ b∈xs,(compare a b).2≤P) :
    (GeneralPaperPricedMergeSort.run compare W depth fuel xs).2+node W depth ≤
      xs.length*(fuel+1)*(P+24*W)+2^(fuel+1)*node W depth := by
  have hNode : 2*W≤node W depth := by unfold node; nlinarith
  induction fuel generalizing xs with
  | zero =>
    simp only [GeneralPaperPricedMergeSort.run,Nat.zero_add,pow_one,Nat.mul_one]
    omega
  | succ fuel ih =>
    have hPower : 2≤2^(fuel+1+1) := by
      calc
        2 = (2 : ℕ)^1 := by decide
        _ ≤ 2^(fuel+1+1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hReserve := Nat.mul_le_mul_right (node W depth) hPower
    cases xs with
    | nil =>
      simp only [GeneralPaperPricedMergeSort.run,List.length_nil,Nat.zero_mul,Nat.zero_add]
      omega
    | cons a xs =>
      cases xs with
      | nil =>
        simp only [GeneralPaperPricedMergeSort.run,List.length_cons,List.length_nil,Nat.zero_add,Nat.one_mul]
        omega
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
          (GeneralPaperPricedMergeSort.run compare W depth fuel halves.left).1
          (GeneralPaperPricedMergeSort.run compare W depth fuel halves.right).1
          (fun x hx y hy => h x (hLeft x ((GeneralPaperPricedMergeSort.mem compare W depth fuel halves.left x).mp hx))
            y (hRight y ((GeneralPaperPricedMergeSort.mem compare W depth fuel halves.right y).mp hy)))
        rw [GeneralPaperPricedMergeSort.length,GeneralPaperPricedMergeSort.length,hs] at hm
        have hp := GeneralPaperPricedSortSplit.work W depth (a::b::rest)
        change halves.work=(16*(a::b::rest).length+26+12*depth)*W at hp
        have hSum := Nat.add_le_add hl hr
        have hFactor : halves.left.length*(fuel+1)*(P+24*W)+halves.right.length*(fuel+1)*(P+24*W)=
            (a::b::rest).length*(fuel+1)*(P+24*W) := by rw [← Nat.add_mul,← Nat.add_mul,hs]
        change (GeneralPaperPricedMergeSort.run compare W depth fuel halves.left).2+
          (GeneralPaperPricedMergeSort.run compare W depth fuel halves.right).2+
          (GeneralPaperPricedMerge.run compare W
            (GeneralPaperPricedMergeSort.run compare W depth fuel halves.left).1
            (GeneralPaperPricedMergeSort.run compare W depth fuel halves.right).1).2+
          halves.work+8*W+node W depth ≤ _
        rw [pow_succ]
        dsimp only [node] at hSum ⊢
        nlinarith only [hSum,hFactor,hm,hp]


def profile (n W P : ℕ) : ℕ :=
  n*(binaryWordWidth (n+1)+2)*(P+24*W)+
    8*(n+1)*(48+12*binaryWordWidth (n+1))*W+(12*binaryWordWidth (n+1)+8*n+20)*W

theorem selected_power (n : ℕ) :
    2^(GeneralPaperRaySearchControls.depth (n+1)+1)≤8*(n+1) := by
  unfold GeneralPaperRaySearchControls.depth
  rw [pow_succ,pow_succ,← GeneralPaperPowerCeiling.ceiling_power]
  have h := GeneralPaperPowerCeiling.ceiling_upper (n+1) (by omega)
  nlinarith only [h]

theorem work {α : Type*} (compare : α → α → Bool×ℕ) (W P : ℕ) (xs : List α)
    (h : ∀ a∈xs,∀ b∈xs,(compare a b).2≤P) :
    (GeneralPaperPricedSort.run compare W xs).2≤profile xs.length W P := by
  let D := GeneralPaperRaySearchControls.depth (xs.length+1)
  let L := binaryWordWidth (xs.length+1)
  have hDepth : D≤L+1 := GeneralPaperRaySearchControls.depth_bound (xs.length+1)
  have ht := tree_work compare W D D P xs h
  have hFirst := Nat.mul_le_mul_right (P+24*W)
    (Nat.mul_le_mul_left xs.length (Nat.add_le_add_right hDepth 1))
  have hn : node W D≤(48+12*L)*W := by unfold node; nlinarith only [hDepth]
  have hp := Nat.mul_le_mul (selected_power xs.length) hn
  have hc := Nat.mul_le_mul_right W (GeneralPaperPowerCeiling.ceiling_work (xs.length+1))
  change (GeneralPaperPricedMergeSort.run compare W D D xs).2+
    (GeneralPaperPowerCeiling.ceiling (xs.length+1)).work*W+(8*xs.length+16)*W≤_
  unfold profile
  dsimp only [L] at hFirst hp hc
  nlinarith only [ht,hFirst,hp,hc,Nat.zero_le (node W D)]

theorem real_profile (n P : ℕ) :
    profile n 1 P≤(P+512)*(n+1)*(binaryWordWidth (n+1)+2) := by
  let L := binaryWordWidth (n+1)
  have h1 := Nat.mul_le_mul_right (P+24) (Nat.mul_le_mul_right (L+2) (Nat.le_succ n))
  have h2 := Nat.mul_le_mul_left (8*(n+1)) (by omega : 48+12*L≤24*(L+2))
  have h3 : 12*L+8*n+20≤32*(n+1)*(L+2) := by nlinarith only [Nat.zero_le (n*L)]
  unfold profile
  dsimp only [L] at h1 h2 h3
  nlinarith only [h1,h2,h3,Nat.zero_le ((n+1)*(L+2))]

theorem real_work {α : Type*} (compare : α → α → Bool×ℕ) (P : ℕ) (xs : List α)
    (h : ∀ a∈xs,∀ b∈xs,(compare a b).2≤P) :
    (GeneralPaperPricedSort.run compare 1 xs).2≤(P+512)*(xs.length+1)*(binaryWordWidth (xs.length+1)+2) :=
  (work compare 1 P xs h).trans (real_profile xs.length P)

end Blotto.PlayerSpecificSortWork
