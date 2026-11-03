import Blotto.GeneralPaperEncodedEpochLevels

/-! Abstract reference vectors with explicitly owned element payloads.
Indexed prefixes reserve only their constructed entries. Borrowed payloads
may be counted separately, by using the zero payload function. -/
namespace Blotto.GeneralPaperEncodedReferenceVector
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def payload {α : Type*} (encode : α → ℕ) (values : Array α) : ℕ := ∑ i : Fin values.size, encode values[i.val]
def footprint {α : Type*} (W : ℕ) (encode : α → ℕ) (values : Array α) : ℕ := payload encode values+values.size*W+64*W

theorem bounded {α : Type*} (W P : ℕ) (encode : α → ℕ) (values : Array α)
    (he : ∀ i : Fin values.size,encode values[i.val]≤P) : footprint W encode values≤values.size*(P+W)+64*W := by
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => he i)
  have hp : payload encode values≤values.size*P := by
    simpa only [payload,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using hs
  unfold footprint
  nlinarith only [hp]

theorem indexed_prefix {α : Type*} {n : ℕ} (index : ℕ → ℕ) (A W P : ℕ) (encode : α → ℕ)
    (callback : Fin n → α × ℕ) (he : ∀ i,encode (callback i).1≤P) (count : ℕ) (hc : count≤n) :
    footprint W encode (PaperIndexedArrayConstruction.fill index A callback count hc).1≤count*(P+W)+64*W := by
  rw [PaperIndexedArrayConstruction.fill_data]
  have h := bounded W P encode (Array.ofFn (fun i : Fin count => (callback ⟨i.val,by omega⟩).1)) (by
    intro i
    rw [Array.getElem_ofFn]
    exact he _)
  simpa only [Array.size_ofFn] using h

theorem capacity_prefix {α : Type*} {n : ℕ} (index : ℕ → ℕ) (A W P : ℕ) (encode : α → ℕ)
    (callback : Fin n → α × ℕ) (he : ∀ i,encode (callback i).1≤P) (count : ℕ) (hc : count≤n) :
    footprint W encode (PaperIndexedArrayConstruction.fill index A callback count hc).1≤n*(P+W)+64*W :=
  (indexed_prefix index A W P encode callback he count hc).trans (Nat.add_le_add_right (Nat.mul_le_mul_right (P+W) hc) _)

theorem borrowed {α : Type*} (W : ℕ) (values : Array α) : footprint W (fun _ => 0) values=values.size*W+64*W := by
  simp only [footprint,payload,Finset.sum_const_zero,Nat.zero_add]

def reservedFootprint {α : Type*} (W capacity : ℕ) (encode : α → ℕ) (values : Array α) : ℕ :=
  payload encode values+capacity*W+64*W

theorem reserved_bound {α : Type*} (W P capacity : ℕ) (encode : α → ℕ) (values : Array α)
    (hc : values.size≤capacity) (he : ∀ i : Fin values.size,encode values[i.val]≤P) :
    reservedFootprint W capacity encode values≤capacity*(P+W)+64*W := by
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => he i)
  have hp : payload encode values≤values.size*P := by
    simpa only [payload,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using hs
  have hn := Nat.mul_le_mul_right P hc
  unfold reservedFootprint
  nlinarith only [hp,hn]

theorem indexed_reserved_prefix {α : Type*} {n : ℕ} (index : ℕ → ℕ) (A W P : ℕ) (encode : α → ℕ)
    (callback : Fin n → α × ℕ) (he : ∀ i,encode (callback i).1≤P) (count : ℕ) (hc : count≤n) :
    reservedFootprint W n encode (PaperIndexedArrayConstruction.fill index A callback count hc).1≤n*(P+W)+64*W := by
  rw [PaperIndexedArrayConstruction.fill_data]
  apply reserved_bound W P n encode _ (by rw [Array.size_ofFn]; exact hc)
  intro i
  rw [Array.getElem_ofFn]
  exact he _

end Blotto.GeneralPaperEncodedReferenceVector
