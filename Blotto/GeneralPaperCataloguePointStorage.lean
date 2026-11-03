import Blotto.GeneralPaperPartitionConstructionStorage

/-! Actual backward reference-list cursor and projected-successor map.
The input array, growing tail, output lists, native projection values and
selected map frames are counted; every cap follows from signed summary codes.
No cursor census or encoding traversal is executed. -/
namespace Blotto.GeneralPaperCataloguePointStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem cursor_members {α : Type*} (data : Array α) (used : ℕ) :
    ∀ x∈(StoredArrayReferenceList.advance data used ⟨data.size,Nat.le_refl _,[]⟩).tail,x∈data.toList := by
  let s := StoredArrayReferenceList.advance data used ⟨data.size,Nat.le_refl _,[]⟩
  have h : StoredArrayReferenceList.into data s.remaining s.bounded s.tail=data.toList :=
    (StoredArrayReferenceList.advance_continuation data used ⟨data.size,Nat.le_refl _,[]⟩).trans
      (StoredArrayReferenceList.list_data data)
  rw [StoredArrayReferenceList.into_data] at h
  intro x hx
  exact h ▸ (List.mem_append.mpr (Or.inr hx))

def cursorFootprint {n : ℕ} (A used : ℕ) (summary : FixedArrayTable n ℕ) : ℕ :=
  let s := StoredArrayReferenceList.advance summary.data used ⟨summary.data.size,Nat.le_refl _,[]⟩
  fields A [s.remaining]+listFootprint A natBits s.tail+64*A

theorem cursor_bound {n : ℕ} (A U used : ℕ) (summary : FixedArrayTable n ℕ)
    (hc : ∀ r,summary.read r<2*U) : cursorFootprint A used summary≤
      n*(natBits (2*U)+2*A)+natBits n+129*A := by
  let s := StoredArrayReferenceList.advance summary.data used ⟨summary.data.size,Nat.le_refl _,[]⟩
  have hm := StoredArrayReferenceList.advance_mass summary.data used ⟨summary.data.size,Nat.le_refl _,[]⟩
  change s.remaining+s.tail.length=summary.data.size+0 at hm
  rw [summary.size] at hm
  have hTail := list_bound A (natBits (2*U)) natBits s.tail (by
    intro x hx
    have h := GeneralPaperCataloguePointExecution.member_code U summary hc x (cursor_members summary.data used x hx)
    exact Nat.add_le_add_left (binaryWordWidth_mono h.le) 1)
  have hLen := Nat.mul_le_mul_right (natBits (2*U)+2*A) (show s.tail.length≤n by omega)
  have hrem : natBits s.remaining≤natBits n := Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1
  unfold cursorFootprint fields
  dsimp only
  change (([s.remaining].map natBits).sum+[s.remaining].length*A+32*A)+listFootprint A natBits s.tail+64*A≤_
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  omega

def mapPeak (A U : ℕ) : List ℕ → ℕ
  | [] => 64*A
  | code::rest =>
      fields A [code,GeneralPaperSignedUpdatePlan.project U code,GeneralPaperSignedUpdatePlan.project U code+1]+
        128*A+mapPeak A U rest

theorem map_bound (A U : ℕ) (xs : List ℕ) (hx : ∀ x∈xs,x<2*U) :
    mapPeak A U xs≤xs.length*(4*natBits (2*U)+192*A)+64*A := by
  induction xs with
  | nil => simp only [mapPeak,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons x xs ih =>
    have hc := hx x (List.mem_cons_self ..)
    have hp := GeneralPaperUnsignedPartition.project_bound U x hc
    have hf := fields_bound A (natBits (2*U))
      [x,GeneralPaperSignedUpdatePlan.project U x,GeneralPaperSignedUpdatePlan.project U x+1] (by
        intro y hy
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
        rcases hy with rfl|rfl|rfl <;> unfold natBits <;>
          exact Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1)
    change _≤3*(natBits (2*U)+A)+32*A at hf
    have hi := ih (fun y hy => hx y (List.mem_cons_of_mem _ hy))
    rw [mapPeak,List.length_cons]
    nlinarith only [hf,hi]

def window {n : ℕ} (model : RationalCostModel) (W U used : ℕ) (summary : FixedArrayTable n ℕ) : ℕ :=
  let values := StoredArrayReferenceList.list summary.data
  let result := GeneralPaperCataloguePointExecution.run true (fun w => w) model.rat W U summary
  GeneralPaperEncodedNatArray.footprint W summary+cursorFootprint W used summary+
    listFootprint W natBits values+2*listFootprint W natBits result.1+mapPeak W U values+result.2+256*W

def profile (model : RationalCostModel) (W U n : ℕ) : ℕ :=
  let P := natBits (2*U)
  n*(P+W)+32*W+(n*(P+2*W)+natBits n+129*W)+(n*(P+2*W)+32*W)+
    2*(n*(natBits U+2*W)+32*W)+(n*(4*P+192*W)+64*W)+
      GeneralPaperCataloguePointPrice.profile model.rat W n U+256*W

theorem bounded {n : ℕ} (model : RationalCostModel) (W U used : ℕ) (summary : FixedArrayTable n ℕ)
    (hc : ∀ r,summary.read r<2*U) : window model W U used summary≤profile model W U n := by
  let values := StoredArrayReferenceList.list summary.data
  let result := GeneralPaperCataloguePointExecution.run true (fun w => w) model.rat W U summary
  have hv : ∀ x∈values,x<2*U := by
    intro x hx
    exact GeneralPaperCataloguePointExecution.member_code U summary hc x
      (by simpa only [values,StoredArrayReferenceList.list_data] using hx)
  have hlen : values.length=n := by
    dsimp only [values]
    rw [StoredArrayReferenceList.list_data,Array.length_toList,summary.size]
  have hi := GeneralPaperEncodedNatArray.bounded_length W (natBits (2*U)) n summary (Nat.le_refl _)
    (fun r => Nat.add_le_add_left (binaryWordWidth_mono (hc r).le) 1)
  have hcursor := cursor_bound W U used summary hc
  have hvalues := list_bound W (natBits (2*U)) natBits values
    (fun x hx => Nat.add_le_add_left (binaryWordWidth_mono (hv x hx).le) 1)
  rw [hlen] at hvalues
  have hout := list_bound W (natBits U) natBits result.1 (by
    intro x hx
    exact Nat.add_le_add_left (binaryWordWidth_mono
      (GeneralPaperCataloguePointExecution.point_bound true (fun w => w) model.rat W U summary hc x hx)) 1)
  have hresult : result.1.length=n := GeneralPaperCataloguePointExecution.length true (fun w => w) model.rat W U summary
  rw [hresult] at hout
  have hm := map_bound W U values hv
  rw [hlen] at hm
  have hs := GeneralPaperCataloguePointPrice.bit_work model.rat model.monotone W U summary hc
  unfold window profile
  dsimp only
  dsimp only [values,result] at *
  omega

end Blotto.GeneralPaperCataloguePointStorage
