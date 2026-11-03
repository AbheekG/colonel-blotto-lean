import Blotto.GeneralPaperEndpointDictionary

/-! Decode original polytope constraints into literal dictionary bounds,
adjacent order, original whole-row budgets and high-tuple exclusion. The
zero anchors are included and repeated/coalescing anchors remain labelled.
-/
namespace Blotto.GeneralPaperEndpointDictionarySemantics
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperSourceEndpointBranch
open GeneralPaperEndpointDictionary GeneralPaperDictionary
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem reference_value {T m K : ℕ} (result : Result T m K) (hK : 0<K) (j : Fin m) (l : Fin K) :
    refValue (fun a => (coordinates result a:ℝ)) (tupleReference j l)=((dictionary result).anchor j l:ℝ) := by
  have hh := GeneralPaperTransferPolytopePoint.coordinate_reference (dictionary result) hK (zero_label result hK) j l
  rwa [real_coordinates] at hh

theorem tuple_value {T m K : ℕ} (result : Result T m K) (hK : 0<K) (ls : Fin m → Fin K) :
    tupleSum (fun a => (coordinates result a:ℝ)) ls=cost (dictionary result) ls := by
  have hh := GeneralPaperTransferPolytopePoint.tuple_sum (dictionary result) hK (zero_label result hK) ls
  rwa [real_coordinates] at hh

theorem anchor_bounds {T m K : ℕ} (result : Result T m K)
    (hBox : ∀ a : Variable m K,0≤(coordinates result a:ℝ) ∧ (coordinates result a:ℝ)≤1)
    (j : Fin m) (l : Fin K) : 0≤(dictionary result).anchor j l ∧ (dictionary result).anchor j l≤1 := by
  by_cases hl : l.val=0
  · change 0≤anchor result j l ∧ anchor result j l≤1
    rw [GeneralPaperEndpointDictionary.anchor,dite_eq_left hl]
    norm_num
  · let v : Variable m K := (j,⟨l.val-1,by have hk := l.isLt; omega⟩)
    have he : GeneralPaperTransferPolytopePoint.positiveLabel v.2=l := by
      apply Fin.ext
      change l.val-1+1=l.val
      omega
    rw [←he,positive_label]
    exact_mod_cast hBox v

theorem ordered {T m K : ℕ} (result : Result T m K) (hK : 0<K)
    (hOrder : ∀ j l,RationalOrderCell.anchor (fun a => (coordinates result a:ℝ)) j (orderLeft l)≤
      RationalOrderCell.anchor (fun a => (coordinates result a:ℝ)) j (orderRight l)) :
    ∀ j,Monotone ((dictionary result).anchor j) := by
  cases K with
  | zero => omega
  | succ n =>
    intro j
    apply Fin.monotone_iff_le_succ.mpr
    intro l
    have hh := hOrder j l
    change refValue (fun a => (coordinates result a:ℝ)) (tupleReference j l.castSucc)≤
      refValue (fun a => (coordinates result a:ℝ)) (tupleReference j l.succ) at hh
    rw [reference_value result hK,reference_value result hK] at hh
    exact_mod_cast hh

theorem rows {T m K : ℕ} (result : Result T m K) (hK : 0<K)
    (hRows : ∀ i,tupleSum (fun a => (coordinates result a:ℝ)) (result.labels i)≤1) :
    ∀ i,∑ j,((dictionary result).anchor j ((dictionary result).label i j):ℝ)≤1 := by
  intro i
  have hh := hRows i
  rw [tuple_value result hK] at hh
  exact hh

theorem high_tuples {T m K : ℕ} (result : Result T m K) (hK : 0<K)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (gamma : ℝ)
    (hHigh : ∀ ls : HighTuple scores h,gamma≤tupleSum (fun a => (coordinates result a:ℝ)) ls.val) :
    ∀ ls : HighTuple scores h,gamma≤cost (dictionary result) ls.val := by
  intro ls
  have hh := hHigh ls
  rwa [tuple_value result hK] at hh

end Blotto.GeneralPaperEndpointDictionarySemantics
