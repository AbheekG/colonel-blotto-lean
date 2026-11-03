import Blotto.GeneralPaperPricedPayloadStreamStorage

/-! Ordinary source list append in the paper reference-cell model. Complete
input/returned payloads, actual borrowed copied prefixes and constructor
control frames are counted. This adds no executable encoding/census pass. -/
namespace Blotto.GeneralPaperPayloadAppendStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def frames {α : Type*} (W : ℕ) : List α → List α → ℕ
  | [],ys => fields W [0,ys.length,ys.length]+128*W
  | a::rest,ys => fields W [(a::rest).length,ys.length,(rest++ys).length,((a::rest)++ys).length]+128*W+frames W rest ys

def frameProfile (W N : ℕ) : ℕ := 4*(natBits N+W)+160*W

theorem frames_bound {α : Type*} (W N : ℕ) (xs ys : List α) (hn : xs.length+ys.length≤N) :
    frames W xs ys≤(xs.length+1)*frameProfile W N := by
  induction xs with
  | nil =>
    have hf := fields_bound W (natBits N) [0,ys.length,ys.length] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl
      all_goals simp only [List.length_nil,Nat.zero_add] at hn; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤3*(natBits N+W)+32*W at hf
    simp only [frames,List.length_nil,Nat.zero_add,Nat.one_mul]
    unfold frameProfile
    omega
  | cons a rest ih =>
    have hr := ih (by simp only [List.length_cons] at hn; omega)
    have hf := fields_bound W (natBits N) [(a::rest).length,ys.length,(rest++ys).length,((a::rest)++ys).length] (by
      intro b hb
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
      rcases hb with rfl|rfl|rfl|rfl
      all_goals simp only [List.length_cons,List.length_append] at hn ⊢; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤4*(natBits N+W)+32*W at hf
    change GeneralPaperEncodedScalarStorage.fields W _+128*W+frames W rest ys≤_
    simp only [List.length_cons] at hf ⊢
    unfold frameProfile at *
    nlinarith only [hf,hr]

def window {α : Type*} (W copied : ℕ) (encode : α → ℕ) (xs ys : List α) : ℕ :=
  listFootprint W encode xs+listFootprint W encode ys+listFootprint W encode (xs++ys)+
    GeneralPaperBorrowedListStorage.footprint W (xs.take copied)+frames W xs ys

def profile (W P N : ℕ) : ℕ := 3*(N*(P+2*W)+32*W)+(2*N*W+32*W)+(N+1)*frameProfile W N

theorem bounded {α : Type*} (W P N copied : ℕ) (encode : α → ℕ) (xs ys : List α)
    (hn : xs.length+ys.length≤N) (hx : ∀ a∈xs,encode a≤P) (hy : ∀ a∈ys,encode a≤P) :
    window W copied encode xs ys≤profile W P N := by
  have hX := (list_bound W P encode xs hx).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (show xs.length≤N by omega)) _)
  have hY := (list_bound W P encode ys hy).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (show ys.length≤N by omega)) _)
  have hZ := (list_bound W P encode (xs++ys) (by
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · exact hx a ha
    · exact hy a ha)).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (by simpa only [List.length_append] using hn)) _)
  have hCopy := GeneralPaperBorrowedListStorage.bounded W N (xs.take copied) (by rw [List.length_take]; have h := Nat.min_le_right copied xs.length; omega)
  have hFrames := (frames_bound W N xs ys hn).trans (Nat.mul_le_mul_right _ (by omega : xs.length+1≤N+1))
  unfold window profile
  omega

end Blotto.GeneralPaperPayloadAppendStorage
