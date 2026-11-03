import Blotto.GeneralPaperPricedMergeSort

/-! Construct and price the complete stable sort, including its fuel. No
encoding-length primitive is run. The logarithmic bound is a theorem about
the doubling construction, not an input to the algorithm.
-/
namespace Blotto.GeneralPaperPricedSort
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run {α : Type*} (compare : α → α → Bool × ℕ) (W : ℕ) (xs : List α) : List α × ℕ :=
  let scale := GeneralPaperPowerCeiling.ceiling (xs.length+1)
  let result := GeneralPaperPricedMergeSort.run compare W (scale.doublings+1) (scale.doublings+1) xs
  (result.1,result.2+scale.work*W+(8*xs.length+16)*W)

theorem data {α : Type*} (compare : α → α → Bool × ℕ) (W : ℕ) (xs : List α) :
    (run compare W xs).1=xs.mergeSort (fun a b => (compare a b).1) := by
  have hs := GeneralPaperRaySearchControls.size_cap (xs.length+1)
  exact GeneralPaperPricedMergeSort.data compare W
    (GeneralPaperRaySearchControls.depth (xs.length+1))
    (GeneralPaperRaySearchControls.depth (xs.length+1)) xs hs (by omega)

theorem perm {α : Type*} (compare : α → α → Bool × ℕ) (W : ℕ) (xs : List α) :
    (run compare W xs).1.Perm xs := by
  rw [data]
  exact List.mergeSort_perm _ _

theorem length {α : Type*} (compare : α → α → Bool × ℕ) (W : ℕ) (xs : List α) :
    (run compare W xs).1.length=xs.length := (perm compare W xs).length_eq

theorem mem {α : Type*} (compare : α → α → Bool × ℕ) (W : ℕ) (xs : List α) (a : α) :
    a∈(run compare W xs).1 ↔ a∈xs := (perm compare W xs).mem_iff

def profile (n W P : ℕ) : ℕ :=
  n*(binaryWordWidth (n+1)+2)*(P+(152+24*binaryWordWidth (n+1))*W)+
    (12*binaryWordWidth (n+1)+8*n+20)*W

theorem work {α : Type*} (compare : α → α → Bool × ℕ) (W P : ℕ) (xs : List α)
    (h : ∀ a∈xs,∀ b∈xs,(compare a b).2≤P) :
    (run compare W xs).2≤profile xs.length W P := by
  have hd := GeneralPaperRaySearchControls.depth_bound (xs.length+1)
  have hr := GeneralPaperPricedMergeSort.work compare W
    (GeneralPaperRaySearchControls.depth (xs.length+1))
    (GeneralPaperRaySearchControls.depth (xs.length+1)) P xs h
  have hc := GeneralPaperPowerCeiling.ceiling_work (xs.length+1)
  have h1 : GeneralPaperRaySearchControls.depth (xs.length+1)+1≤binaryWordWidth (xs.length+1)+2 := by omega
  have h2 : P+(128+24*GeneralPaperRaySearchControls.depth (xs.length+1))*W≤
      P+(152+24*binaryWordWidth (xs.length+1))*W := by nlinarith only [hd]
  have hm := Nat.mul_le_mul (Nat.mul_le_mul_left xs.length h1) h2
  have hs := Nat.mul_le_mul_right W hc
  change (GeneralPaperPricedMergeSort.run compare W
    (GeneralPaperRaySearchControls.depth (xs.length+1))
    (GeneralPaperRaySearchControls.depth (xs.length+1)) xs).2+
    (GeneralPaperPowerCeiling.ceiling (xs.length+1)).work*W+(8*xs.length+16)*W≤_
  unfold profile
  nlinarith only [hr,hm,hs]

theorem profile_mono {n m W P : ℕ} (h : n≤m) : profile n W P≤profile m W P := by
  have hw := binaryWordWidth_mono (Nat.add_le_add_right h 1)
  have hp : P+(152+24*binaryWordWidth (n+1))*W≤P+(152+24*binaryWordWidth (m+1))*W := by
    nlinarith only [hw]
  have hm := Nat.mul_le_mul (Nat.mul_le_mul h (Nat.add_le_add_right hw 2)) hp
  have hc : (12*binaryWordWidth (n+1)+8*n+20)*W≤(12*binaryWordWidth (m+1)+8*m+20)*W :=
    Nat.mul_le_mul_right W (by omega)
  exact Nat.add_le_add hm hc

end Blotto.GeneralPaperPricedSort
