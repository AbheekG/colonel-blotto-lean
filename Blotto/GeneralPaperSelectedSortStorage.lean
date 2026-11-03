import Blotto.GeneralPaperSortWorkMetadataStorage
import Blotto.GeneralPaperCeilingConstructionStorage

/-! Complete selected-fuel native sort window. The actual doubling loop,
recursive payload/merge/split windows and outer encoded work counters are
joined. The analytical index bound never enters the executable sort. -/
namespace Blotto.GeneralPaperSelectedSortStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def depth (N : ℕ) : ℕ := binaryWordWidth (N+1)+1
def metadataCap (W C N : ℕ) : ℕ := N+depth N+1+GeneralPaperPricedSort.profile N W C

def window {α : Type*} (model : RationalCostModel) (W : ℕ) (encode : α → ℕ)
    (compare : α → α → Bool×ℕ) (xs : List α) : ℕ :=
  let n := xs.length
  let scale := GeneralPaperPowerCeiling.ceiling (n+1)
  let d := scale.doublings+1
  let sorted := GeneralPaperPricedMergeSort.run compare W d d xs
  let result := GeneralPaperPricedSort.run compare W xs
  GeneralPaperSortWorkMetadataStorage.window model W encode compare d d xs+
    GeneralPaperCeilingConstructionStorage.peak W (n+1) 1 (by decide)+
    fields W [n+1,d,sorted.2,result.2,scale.work*W,(8*n+16)*W,sorted.2+scale.work*W]+256*W

def profile (model : RationalCostModel) (W P C N : ℕ) : ℕ :=
  GeneralPaperSortWorkMetadataStorage.profile model W P C (depth N) (depth N) N+
    depth N*(5*GeneralPaperCeilingConstructionStorage.word (N+1)+192*W)+
    7*(natBits (metadataCap W C N)+W)+32*W+256*W

theorem profile_mono (model : RationalCostModel) (W P C n N : ℕ) (hn : n≤N) :
    profile model W P C n≤profile model W P C N := by
  have hd : depth n≤depth N := Nat.add_le_add_right (binaryWordWidth_mono (Nat.add_le_add_right hn 1)) 1
  have hi := GeneralPaperSortWorkMetadataStorage.profile_mono model W P C (depth n) (depth N) (depth n) (depth N) n N hd hd hn
  have hw := GeneralPaperPricedSort.profile_mono (W:=W) (P:=C) hn
  unfold profile metadataCap GeneralPaperCeilingConstructionStorage.word natBits
  gcongr

theorem actual {α : Type*} (model : RationalCostModel) (W P C : ℕ) (encode : α → ℕ)
    (compare : α → α → Bool×ℕ) (xs : List α)
    (he : ∀ a∈xs,encode a≤P) (hc : ∀ a∈xs,∀ b∈xs,(compare a b).2≤C) :
    window model W encode compare xs≤profile model W P C xs.length := by
  let n := xs.length
  let scale := GeneralPaperPowerCeiling.ceiling (n+1)
  let d := scale.doublings+1
  let sorted := GeneralPaperPricedMergeSort.run compare W d d xs
  let result := GeneralPaperPricedSort.run compare W xs
  have hd : d≤depth n := GeneralPaperRaySearchControls.depth_bound (n+1)
  have hs : n+1<2^d := GeneralPaperRaySearchControls.size_cap (n+1)
  have hi := GeneralPaperSortWorkMetadataStorage.complete model W P C d d n encode compare xs le_rfl le_rfl hs he hc
  have hi' := hi.trans (GeneralPaperSortWorkMetadataStorage.profile_mono model W P C d (depth n) d (depth n) n n hd hd le_rfl)
  have hCeiling := GeneralPaperCeilingConstructionStorage.bounded W (n+1) 1 (by decide) (by omega)
  change GeneralPaperCeilingConstructionStorage.peak W (n+1) 1 (by decide)≤d*(5*GeneralPaperCeilingConstructionStorage.word (n+1)+192*W) at hCeiling
  have hCeiling' := hCeiling.trans (Nat.mul_le_mul_right _ hd)
  have hWork := GeneralPaperPricedSort.work compare W C xs hc
  change result.2≤GeneralPaperPricedSort.profile n W C at hWork
  have hShape : result.2=sorted.2+scale.work*W+(8*n+16)*W := rfl
  have hFields := fields_bound W (natBits (metadataCap W C n))
    [n+1,d,sorted.2,result.2,scale.work*W,(8*n+16)*W,sorted.2+scale.work*W] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤7*(natBits (metadataCap W C n)+W)+32*W at hFields
  change GeneralPaperSortWorkMetadataStorage.window model W encode compare d d xs+
    GeneralPaperCeilingConstructionStorage.peak W (n+1) 1 (by decide)+
    GeneralPaperEncodedScalarStorage.fields W [n+1,d,sorted.2,result.2,scale.work*W,(8*n+16)*W,sorted.2+scale.work*W]+256*W≤profile model W P C n
  unfold profile
  omega

theorem bounded {α : Type*} (model : RationalCostModel) (W P C N : ℕ) (encode : α → ℕ)
    (compare : α → α → Bool×ℕ) (xs : List α) (hn : xs.length≤N)
    (he : ∀ a∈xs,encode a≤P) (hc : ∀ a∈xs,∀ b∈xs,(compare a b).2≤C) :
    window model W encode compare xs≤profile model W P C N :=
  (actual model W P C encode compare xs he hc).trans (profile_mono model W P C xs.length N hn)

end Blotto.GeneralPaperSelectedSortStorage
