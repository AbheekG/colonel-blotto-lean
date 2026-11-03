import Blotto.GeneralPaperEpochResidentStorage

/-! Erased storage observers for scalar records and owned linked lists.
The list observer counts head/tail references and its descriptor. These
lists are analysis of existing fields; no metadata traversal executes. -/
namespace Blotto.GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def natBits (x : ℕ) : ℕ := 1+binaryWordWidth x

def listFootprint {α : Type*} (W : ℕ) (encode : α → ℕ) (xs : List α) : ℕ :=
  (xs.map encode).sum+xs.length*(2*W)+32*W

theorem sum_bound {α : Type*} (encode : α → ℕ) (P : ℕ) (xs : List α)
    (h : ∀ x∈xs,encode x≤P) : (xs.map encode).sum≤xs.length*P := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (List.mem_cons_self ..)
    have hs := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simpa only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,one_mul,Nat.add_comm] using Nat.add_le_add hx hs

theorem list_bound {α : Type*} (W P : ℕ) (encode : α → ℕ) (xs : List α)
    (h : ∀ x∈xs,encode x≤P) : listFootprint W encode xs≤xs.length*(P+2*W)+32*W := by
  have hs := sum_bound encode P xs h
  unfold listFootprint
  nlinarith only [hs]

def fields (W : ℕ) (xs : List ℕ) : ℕ := (xs.map natBits).sum+xs.length*W+32*W

theorem fields_bound (W P : ℕ) (xs : List ℕ) (h : ∀ x∈xs,natBits x≤P) :
    fields W xs≤xs.length*(P+W)+32*W := by
  have hs := sum_bound natBits P xs h
  unfold fields
  nlinarith only [hs]

end Blotto.GeneralPaperEncodedScalarStorage
