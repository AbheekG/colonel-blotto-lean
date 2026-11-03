import Blotto.GeneralPaperEncodedProfitTree

/-! Reference-list buffers borrow existing element payloads. Splitting
copies only prefix cells, with the original list, returned take/drop and
one in-progress copied prefix all included. -/
namespace Blotto.GeneralPaperBorrowedListStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def footprint {α : Type*} (W : ℕ) (xs : List α) : ℕ :=
  GeneralPaperEncodedScalarStorage.listFootprint W (fun _ => 0) xs

theorem exact_size {α : Type*} (W : ℕ) (xs : List α) : footprint W xs=2*xs.length*W+32*W := by
  unfold footprint GeneralPaperEncodedScalarStorage.listFootprint
  simp only [List.map_const',List.sum_replicate]
  ring

theorem bounded {α : Type*} (W N : ℕ) (xs : List α) (hn : xs.length≤N) : footprint W xs≤2*N*W+32*W := by
  rw [exact_size]
  nlinarith only [Nat.mul_le_mul_right W hn]

def splitWindow {α : Type*} (W : ℕ) (xs : List α) (count progress : ℕ) : ℕ :=
  footprint W xs+footprint W (xs.take count)+footprint W (xs.drop count)+footprint W ((xs.take count).take progress)

theorem split_window {α : Type*} (W N count progress : ℕ) (xs : List α) (hn : xs.length≤N) :
    splitWindow W xs count progress≤6*N*W+128*W := by
  have hl : (xs.take count).length+(xs.drop count).length=xs.length := by
    rw [←List.length_append,List.take_append_drop]
  have hp : ((xs.take count).take progress).length≤N := by simp only [List.length_take]; omega
  have h := Nat.mul_le_mul_right W hn
  have h' := Nat.mul_le_mul_right W hp
  simp only [splitWindow,exact_size]
  nlinarith only [hl,h,h']

theorem priced_split {α : Type*} (primitive : ℕ → ℕ) (W N count progress : ℕ) (xs : List α) (hn : xs.length≤N) :
    let parts := (GeneralPaperPricedListSplit.run primitive W count xs).1
    footprint W xs+footprint W parts.1+footprint W parts.2+footprint W (parts.1.take progress)≤6*N*W+128*W := by
  rw [GeneralPaperPricedListSplit.data]
  exact split_window W N count progress xs hn

end Blotto.GeneralPaperBorrowedListStorage
