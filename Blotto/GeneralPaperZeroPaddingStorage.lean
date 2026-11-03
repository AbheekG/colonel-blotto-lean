import Blotto.GeneralPaperProfitListConstructionStorage

/-! One shared zero-profit field is built with all reserved slots counted.
Padding and append copy references to existing weighted fields. Their
source-retained span and field count derive every list-capacity premise. -/
namespace Blotto.GeneralPaperZeroPaddingStorage
open GeneralPaperResponseTag GeneralPaperOrderedProfitTreeBuild
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem zero_prefix (index : ℕ → ℕ) (W A K s count : ℕ) (hs : 0<s) (hc : count≤K) :
    GeneralPaperEncodedReferenceVector.reservedFootprint W K (GeneralPaperEncodedProfitField.optionBits W)
      (PaperIndexedArrayConstruction.fill index A (fun _ : Fin K => (((0,(0:Tag)),64*A))) count hc).1≤
        K*(2+(1+2*s)+1+25*W)+64*W := by
  have ht := rationalWordWidth_of_height (GeneralPaperTagHeight.zero_height s hs)
  have hf := GeneralPaperEncodedReferenceVector.indexed_reserved_prefix index A W (2+(1+2*s)+1+24*W)
    (GeneralPaperEncodedProfitField.optionBits W) (fun _ : Fin K => (((0,(0:Tag)),64*A))) (by
      intro i
      change 2+rationalWordWidth (0:Tag).threshold+1+24*W≤_
      omega) count hc
  exact hf.trans_eq (by ring)

theorem padding_prefix {K : ℕ} (index : ℕ → ℕ) (W A span m remaining : ℕ) (zero : WeightedField Tag K)
    (h : remaining≤span-m) (xs : List (WeightedField Tag K)) (hn : remaining+xs.length=span-m) :
    GeneralPaperBorrowedListStorage.footprint W
      (GeneralPaperIndexedListPrice.fill index A (fun _ : Fin (span-m) => (zero,64*W)) remaining h xs).1≤2*span*W+32*W := by
  apply GeneralPaperBorrowedListStorage.bounded
  rw [GeneralPaperIndexedListPrice.every_prefix,hn]
  exact Nat.sub_le _ _

def appendWindow {K : ℕ} (W : ℕ) (input padding : List (WeightedField Tag K)) (copied : ℕ) : ℕ :=
  GeneralPaperBorrowedListStorage.footprint W input+GeneralPaperBorrowedListStorage.footprint W padding+
    GeneralPaperBorrowedListStorage.footprint W (GeneralPaperPricedListAppend.run W input padding).1+
    GeneralPaperBorrowedListStorage.footprint W (input.take copied)+input.length*(64*W)+128*W

theorem append_bound {K : ℕ} (W span m copied : ℕ) (input padding : List (WeightedField Tag K))
    (hm : input.length=m) (hp : padding.length=span-m) (hfit : m≤span) : appendWindow W input padding copied≤72*span*W+256*W := by
  have hi : input.length≤span := hm.trans_le hfit
  have hpad : padding.length≤span := by rw [hp]; exact Nat.sub_le _ _
  have hout : (GeneralPaperPricedListAppend.run W input padding).1.length≤span := by
    rw [GeneralPaperPricedListAppend.data,List.length_append,hm,hp]
    omega
  have hcopy : (input.take copied).length≤span := by rw [List.length_take]; exact (Nat.min_le_right _ _).trans hi
  have h1 := GeneralPaperBorrowedListStorage.bounded W span input hi
  have h2 := GeneralPaperBorrowedListStorage.bounded W span padding hpad
  have h3 := GeneralPaperBorrowedListStorage.bounded W span _ hout
  have h4 := GeneralPaperBorrowedListStorage.bounded W span _ hcopy
  have h5 := Nat.mul_le_mul_right (64*W) hi
  unfold appendWindow
  nlinarith only [h1,h2,h3,h4,h5]

theorem native_padding {K : ℕ} (index : ℕ → ℕ) (W A span m copied : ℕ) (zero : WeightedField Tag K)
    (input : List (WeightedField Tag K)) (hm : input.length=m) (hfit : m≤span) :
    appendWindow W input (GeneralPaperIndexedListPrice.run index A (fun _ : Fin (span-m) => (zero,64*W))).1 copied≤72*span*W+256*W := by
  apply append_bound W span m copied input _ hm _ hfit
  rw [GeneralPaperIndexedListPrice.data,List.length_ofFn]

theorem source_padding {m K : ℕ} (index : ℕ → ℕ) (W A lambda k Qv copied : ℕ)
    (input : List (WeightedField Tag K)) (hm : input.length=m) :
    let span := (GeneralPaperProfitParameters.parameters m lambda k Qv).leafCount
    appendWindow W input (GeneralPaperIndexedListPrice.run index A (fun _ : Fin (span-m) => (dummy Tag K,64*W))).1 copied≤
      72*span*W+256*W :=
  native_padding index W A _ m copied (dummy Tag K) input hm (GeneralPaperProfitParameters.covers_fields m lambda k Qv)

end Blotto.GeneralPaperZeroPaddingStorage
