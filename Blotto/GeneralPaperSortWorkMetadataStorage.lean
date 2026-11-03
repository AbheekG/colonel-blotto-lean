import Blotto.GeneralPaperMergeWorkMetadataStorage
import Blotto.GeneralPaperBorrowedListStorage

/-! Native merge-sort metadata and literal split-midpoint scratch, added
to the checked payload/structural-frame window. A split prefix is reserved
once; sibling histories do not accumulate. Work counters contribute only
their encoded lengths. The outer selected-fuel wrapper is a separate join. -/
namespace Blotto.GeneralPaperSortWorkMetadataStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def workCap (W C depth N : ℕ) : ℕ := N*(depth+1)*(C+(128+24*depth)*W)+2*W
def metadataCap (W C depth N : ℕ) : ℕ := N+depth+1+workCap W C depth N
def frameProfile (W C depth N : ℕ) : ℕ := 11*(natBits (metadataCap W C depth N)+W)+160*W

theorem work_bound {α : Type*} (compare : α → α → Bool×ℕ) (W C depth fuel N : ℕ) (xs : List α)
    (hf : fuel≤depth) (hn : xs.length≤N) (hc : ∀ a∈xs,∀ b∈xs,(compare a b).2≤C) :
    (GeneralPaperPricedMergeSort.run compare W depth fuel xs).2≤workCap W C depth N :=
  (GeneralPaperPricedMergeSort.work compare W depth fuel C xs hc).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul hn (Nat.add_le_add_right hf 1))) _)

def baseFrame {α : Type*} (compare : α → α → Bool×ℕ) (W depth fuel : ℕ) (xs : List α) : ℕ :=
  fields W [depth,fuel,xs.length,(GeneralPaperPricedMergeSort.run compare W depth fuel xs).2]+128*W

theorem base_bound {α : Type*} (compare : α → α → Bool×ℕ) (W C depth fuel N : ℕ) (xs : List α)
    (hf : fuel≤depth) (hn : xs.length≤N) (hc : ∀ a∈xs,∀ b∈xs,(compare a b).2≤C) :
    baseFrame compare W depth fuel xs≤frameProfile W C depth N := by
  have hw := work_bound compare W C depth fuel N xs hf hn hc
  have hs := fields_bound W (natBits (metadataCap W C depth N))
    [depth,fuel,xs.length,(GeneralPaperPricedMergeSort.run compare W depth fuel xs).2] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤4*(natBits (metadataCap W C depth N)+W)+32*W at hs
  unfold baseFrame frameProfile
  omega

def frame {α : Type*} (compare : α → α → Bool×ℕ) (W depth fuel : ℕ) (x y : α) (rest : List α) : ℕ :=
  let xs := x::y::rest
  let halves := GeneralPaperPricedSortSplit.run W depth xs
  let left := GeneralPaperPricedMergeSort.run compare W depth fuel halves.left
  let right := GeneralPaperPricedMergeSort.run compare W depth fuel halves.right
  let merged := GeneralPaperPricedMerge.run compare W left.1 right.1
  let result := GeneralPaperPricedMergeSort.run compare W depth (fuel+1) xs
  fields W [depth,fuel+1,xs.length,left.2,right.2,merged.2,halves.work,result.2,
    left.2+right.2,left.2+right.2+merged.2,left.2+right.2+merged.2+halves.work]+128*W

theorem frame_bound {α : Type*} (compare : α → α → Bool×ℕ) (W C depth fuel N : ℕ) (x y : α) (rest : List α)
    (hf : fuel+1≤depth) (hn : (x::y::rest).length≤N) (hc : ∀ a∈x::y::rest,∀ b∈x::y::rest,(compare a b).2≤C) :
    frame compare W depth fuel x y rest≤frameProfile W C depth N := by
  let xs := x::y::rest
  let halves := GeneralPaperPricedSortSplit.run W depth xs
  let left := GeneralPaperPricedMergeSort.run compare W depth fuel halves.left
  let right := GeneralPaperPricedMergeSort.run compare W depth fuel halves.right
  let merged := GeneralPaperPricedMerge.run compare W left.1 right.1
  let result := GeneralPaperPricedMergeSort.run compare W depth (fuel+1) xs
  have hw := work_bound compare W C depth (fuel+1) N xs hf hn hc
  change xs.length≤N at hn
  change result.2≤workCap W C depth N at hw
  have hShape : result.2=left.2+right.2+merged.2+halves.work+8*W := rfl
  have hs := fields_bound W (natBits (metadataCap W C depth N))
    [depth,fuel+1,xs.length,left.2,right.2,merged.2,halves.work,result.2,
      left.2+right.2,left.2+right.2+merged.2,left.2+right.2+merged.2+halves.work] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤11*(natBits (metadataCap W C depth N)+W)+32*W at hs
  change GeneralPaperEncodedScalarStorage.fields W
    [depth,fuel+1,xs.length,left.2,right.2,merged.2,halves.work,result.2,
      left.2+right.2,left.2+right.2+merged.2,left.2+right.2+merged.2+halves.work]+128*W≤_
  unfold frameProfile
  omega

def peak {α : Type*} (model : RationalCostModel) (compare : α → α → Bool×ℕ) (W depth : ℕ) : ℕ → List α → ℕ
  | 0,xs => baseFrame compare W depth 0 xs
  | fuel+1,[] => baseFrame compare W depth (fuel+1) []
  | fuel+1,[x] => baseFrame compare W depth (fuel+1) [x]
  | fuel+1,x::y::rest =>
    let xs := x::y::rest
    let halves := GeneralPaperPricedSortSplit.run W depth xs
    let left := (GeneralPaperPricedMergeSort.run compare W depth fuel halves.left).1
    let right := (GeneralPaperPricedMergeSort.run compare W depth fuel halves.right).1
    frame compare W depth fuel x y rest+GeneralPaperRankMidpointStorage.window model W depth 0 (xs.length+1)+
      GeneralPaperBorrowedListStorage.splitWindow W xs (GeneralPaperPricedSortSplit.cut depth xs) xs.length+
      max (peak model compare W depth fuel halves.left)
        (max (peak model compare W depth fuel halves.right) (GeneralPaperMergeWorkMetadataStorage.peak compare W left right))

def coefficient (model : RationalCostModel) (W C depth N : ℕ) : ℕ :=
  frameProfile W C depth N+GeneralPaperRankMidpointStorage.profile model W depth (N+1)+
    (6*N*W+128*W)+GeneralPaperMergeWorkMetadataStorage.profile W C N

theorem bounded {α : Type*} (model : RationalCostModel) (compare : α → α → Bool×ℕ) (W C depth fuel N : ℕ)
    (xs : List α) (hf : fuel≤depth) (hn : xs.length≤N) (hs : N+1<2^depth)
    (hc : ∀ a∈xs,∀ b∈xs,(compare a b).2≤C) :
    peak model compare W depth fuel xs≤(fuel+1)*coefficient model W C depth N := by
  have hFrameCap : frameProfile W C depth N≤coefficient model W C depth N := by unfold coefficient; omega
  induction fuel generalizing xs with
  | zero =>
    simpa only [peak,Nat.zero_add,Nat.one_mul] using (base_bound compare W C depth 0 N xs (by omega) hn hc).trans hFrameCap
  | succ fuel ih =>
    cases xs with
    | nil =>
      exact ((base_bound compare W C depth (fuel+1) N [] hf hn hc).trans hFrameCap).trans (Nat.le_mul_of_pos_left _ (by omega))
    | cons x rest =>
      cases rest with
      | nil =>
        exact ((base_bound compare W C depth (fuel+1) N [x] hf hn hc).trans hFrameCap).trans (Nat.le_mul_of_pos_left _ (by omega))
      | cons y rest =>
        let xs := x::y::rest
        let halves := GeneralPaperPricedSortSplit.run W depth xs
        let left := (GeneralPaperPricedMergeSort.run compare W depth fuel halves.left).1
        let right := (GeneralPaperPricedMergeSort.run compare W depth fuel halves.right).1
        have hLengths := GeneralPaperPricedSortSplit.lengths W depth xs
        change halves.left.length+halves.right.length=xs.length at hLengths
        have hLeft : ∀ a∈halves.left,a∈xs := fun a ha => GeneralPaperPricedSortSplit.left_mem W depth xs a ha
        have hRight : ∀ a∈halves.right,a∈xs := fun a ha => GeneralPaperPricedSortSplit.right_mem W depth xs a ha
        have hl := ih halves.left (by omega) (by dsimp only [xs] at hLengths; omega)
          (fun a ha b hb => hc a (hLeft a ha) b (hLeft b hb))
        have hr := ih halves.right (by omega) (by dsimp only [xs] at hLengths; omega)
          (fun a ha b hb => hc a (hRight a ha) b (hRight b hb))
        have hLeftMem : ∀ a∈left,a∈xs := fun a ha => hLeft a ((GeneralPaperPricedMergeSort.mem compare W depth fuel halves.left a).mp ha)
        have hRightMem : ∀ a∈right,a∈xs := fun a ha => hRight a ((GeneralPaperPricedMergeSort.mem compare W depth fuel halves.right a).mp ha)
        have hOutLength : left.length+right.length≤N := by
          dsimp only [left,right]
          rw [GeneralPaperPricedMergeSort.length,GeneralPaperPricedMergeSort.length,hLengths]
          exact hn
        have hm := GeneralPaperMergeWorkMetadataStorage.complete compare W C N left right hOutLength
          (fun a ha b hb => hc a (hLeftMem a ha) b (hRightMem b hb))
        have hm' : GeneralPaperMergeWorkMetadataStorage.peak compare W left right≤(fuel+1)*coefficient model W C depth N := by
          have hC : GeneralPaperMergeWorkMetadataStorage.profile W C N≤coefficient model W C depth N := by unfold coefficient; omega
          exact (hm.trans hC).trans (Nat.le_mul_of_pos_left _ (by omega))
        have hF := frame_bound compare W C depth fuel N x y rest hf hn hc
        have hM := GeneralPaperRankMidpointStorage.bounded model W depth (N+1) 0 (xs.length+1) (by omega)
          (Nat.add_le_add_right hn 1) hs
        have hS := GeneralPaperBorrowedListStorage.split_window W N (GeneralPaperPricedSortSplit.cut depth xs) xs.length xs hn
        have hLocal : frame compare W depth fuel x y rest+GeneralPaperRankMidpointStorage.window model W depth 0 (xs.length+1)+
            GeneralPaperBorrowedListStorage.splitWindow W xs (GeneralPaperPricedSortSplit.cut depth xs) xs.length≤coefficient model W C depth N := by
          unfold coefficient
          omega
        change frame compare W depth fuel x y rest+GeneralPaperRankMidpointStorage.window model W depth 0 (xs.length+1)+
          GeneralPaperBorrowedListStorage.splitWindow W xs (GeneralPaperPricedSortSplit.cut depth xs) xs.length+max _ (max _ _)≤_
        have hMax := max_le hl (max_le hr hm')
        exact (Nat.add_le_add hLocal hMax).trans_eq (by ring)

def window {α : Type*} (model : RationalCostModel) (W : ℕ) (encode : α → ℕ) (compare : α → α → Bool×ℕ)
    (depth fuel : ℕ) (xs : List α) : ℕ :=
  GeneralPaperSortConstructionStorage.peak W encode compare depth fuel xs+peak model compare W depth fuel xs

def profile (model : RationalCostModel) (W P C depth fuel N : ℕ) : ℕ :=
  (fuel+1)*(GeneralPaperSortConstructionStorage.coefficient W P C depth N+coefficient model W C depth N)

theorem profile_mono (model : RationalCostModel) (W P C d e f g n N : ℕ)
    (hd : d≤e) (hf : f≤g) (hn : n≤N) :
    profile model W P C d f n≤profile model W P C e g N := by
  unfold profile coefficient frameProfile metadataCap workCap
    GeneralPaperSortConstructionStorage.coefficient GeneralPaperSortConstructionStorage.controlWord
    GeneralPaperSortConstructionStorage.controlCap GeneralPaperRankMidpointStorage.profile
    GeneralPaperRankMidpointStorage.argumentHeight GeneralPaperRankMidpointStorage.metadataCap
    GeneralPaperQuotientConstructionStorage.frameCap GeneralPaperQuotientConstructionStorage.localCap
    GeneralPaperBoundedQuotient.heightBudget GeneralPaperMergeWorkMetadataStorage.profile
    GeneralPaperMergeWorkMetadataStorage.frameProfile GeneralPaperMergeWorkMetadataStorage.metadataCap
    GeneralPaperMergeWorkMetadataStorage.workCap natBits
  dsimp only
  gcongr <;> (apply model.monotone; gcongr)

theorem complete {α : Type*} (model : RationalCostModel) (W P C depth fuel N : ℕ) (encode : α → ℕ)
    (compare : α → α → Bool×ℕ) (xs : List α) (hf : fuel≤depth) (hn : xs.length≤N) (hs : N+1<2^depth)
    (he : ∀ a∈xs,encode a≤P) (hc : ∀ a∈xs,∀ b∈xs,(compare a b).2≤C) :
    window model W encode compare depth fuel xs≤profile model W P C depth fuel N := by
  have hData := GeneralPaperSortConstructionStorage.bounded W P C depth fuel N encode compare xs hf hn hs he hc
  have hMetadata := bounded model compare W C depth fuel N xs hf hn hs hc
  exact (Nat.add_le_add hData hMetadata).trans_eq (by unfold profile; ring)

end Blotto.GeneralPaperSortWorkMetadataStorage
