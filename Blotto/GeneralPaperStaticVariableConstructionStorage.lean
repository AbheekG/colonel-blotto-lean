import Blotto.GeneralPaperPayloadAppendStorage

/-! Actual native static variable enumeration: inner label maps, outer
field flatMap, current variable segments/append copies, range constructors
and encoded native wrapper prices. One active inner map is reserved. -/
namespace Blotto.GeneralPaperStaticVariableConstructionStorage
open RationalOrderCell GeneralPaperStaticRayRows GeneralPaperEncodedScalarStorage
open GeneralPaperPricedPayloadStreamStorage
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def variableFoot {m K : ℕ} (W : ℕ) (v : Variable m K) : ℕ := GeneralPaperStaticRowResidualStorage.variableFoot W v
def variableProfile (W m K : ℕ) : ℕ := 2*natBits (m+K+1)+32*W

theorem variable_bound {m K : ℕ} (W : ℕ) (v : Variable m K) : variableFoot W v≤variableProfile W m K := by
  have hm := v.1.isLt
  have hK := v.2.isLt
  have ha := Nat.add_le_add_left (binaryWordWidth_mono (show v.1.val≤m+K+1 by omega)) 1
  have hb := Nat.add_le_add_left (binaryWordWidth_mono (show v.2.val≤m+K+1 by omega)) 1
  unfold variableFoot variableProfile GeneralPaperStaticRowResidualStorage.variableFoot
  unfold natBits at *
  omega

def labels {m : ℕ} (W K : ℕ) (j : Fin m) : List (Variable m K)×ℕ :=
  GeneralPaperPricedListMap.run W (fun l => ((j,l),8*W)) (List.finRange (K-1))
def rowReturn {m : ℕ} (W K : ℕ) (j : Fin m) : List (Variable m K)×ℕ :=
  let current := labels W K j
  (current.1,current.2+16*((K-1)+1)*W)
def rowPrice (W K : ℕ) : ℕ := (32*(K-1)+18)*W

theorem row_work {m : ℕ} (W K : ℕ) (j : Fin m) : (rowReturn W K j).2≤rowPrice W K := by
  have h := GeneralPaperPricedListMap.work W (8*W) (fun l => ((j,l),8*W)) (List.finRange (K-1)) (fun _ _ => le_rfl)
  simp only [List.length_finRange] at h
  change (labels W K j).2+16*((K-1)+1)*W≤_
  change (labels W K j).2≤_ at h
  unfold rowPrice
  nlinarith only [h]

def innerCap (W m K : ℕ) : ℕ := m+K+1+2*rowPrice W K+16*((K-1)+1)*W+8*W

def innerWindow {m : ℕ} (W K : ℕ) (j : Fin m) (active : Option (Fin (K-1))) : ℕ :=
  mapWindow W (variableFoot W) (fun l => ((j,l),8*W)) (fun _ => 0) active (List.finRange (K-1))+
    fields W [j.val,(labels W K j).2,(rowReturn W K j).2,16*((K-1)+1)*W,8*W]+128*W

def innerProfile (W m K : ℕ) : ℕ := filterProfile W (variableProfile W m K) (8*W) (K-1) 0+
  5*(natBits (innerCap W m K)+W)+160*W

theorem inner_bound {m : ℕ} (W K : ℕ) (j : Fin m) (active : Option (Fin (K-1))) :
    innerWindow W K j active≤ innerProfile W m K := by
  have hMap := map_bounded W (variableProfile W m K) (8*W) (K-1) 0 (variableFoot W) (fun l => ((j,l),8*W))
    (fun _ => 0) active (List.finRange (K-1)) (by simp only [List.length_finRange,le_refl])
    (fun _ _ => le_rfl) (fun l _ => variable_bound W (j,l)) (fun _ _ => le_rfl) (fun l _ => List.mem_finRange l)
  have hWork := row_work W K j
  have hShape : (rowReturn W K j).2=(labels W K j).2+16*((K-1)+1)*W := rfl
  have hj := j.isLt
  have hf := fields_bound W (natBits (innerCap W m K)) [j.val,(labels W K j).2,(rowReturn W K j).2,16*((K-1)+1)*W,8*W] (by
    intro a ha
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl
    all_goals unfold innerCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤5*(natBits (innerCap W m K)+W)+32*W at hf
  unfold innerWindow innerProfile
  omega

def price (W m K : ℕ) : ℕ := 128*(m*(K-1)+m+1)*W
def callerCap (W m K : ℕ) : ℕ := m+K+1+2*price W m K+16*(m+1)*W

def window (W m K copied : ℕ) (activeField : Option (Fin m)) (activeLabel : Option (Fin (K-1))) : ℕ :=
  let body := GeneralPaperPricedListStream.flatMap W (rowReturn W K) (List.finRange m)
  let result := GeneralPaperStaticEnumerationPrice.variableRun W m K
  flatWindow W copied (variableFoot W) (rowReturn W K) (fun j => innerWindow W K j activeLabel) activeField (List.finRange m)+
    GeneralPaperFinRangeStorage.window W m copied+GeneralPaperFinRangeStorage.window W (K-1) copied+
    fields W [m,K,body.2,result.2,16*(m+1)*W]+128*W

def profile (W m K : ℕ) : ℕ :=
  flatProfile W (variableProfile W m K) (K-1) (rowPrice W K) m (innerProfile W m K)+
    GeneralPaperFinRangeStorage.profile W m+GeneralPaperFinRangeStorage.profile W (K-1)+
    5*(natBits (callerCap W m K)+W)+160*W

theorem bounded (W m K copied : ℕ) (activeField : Option (Fin m)) (activeLabel : Option (Fin (K-1))) :
    window W m K copied activeField activeLabel≤profile W m K := by
  let body := GeneralPaperPricedListStream.flatMap W (rowReturn W K) (List.finRange m)
  let result := GeneralPaperStaticEnumerationPrice.variableRun W m K
  have hLength (j : Fin m) : (rowReturn W K j).1.length=K-1 := by
    simp only [rowReturn,labels,GeneralPaperPricedListMap.length,List.length_finRange]
  have hPayload (j : Fin m) (v : Variable m K) (_hv : v∈(rowReturn W K j).1) : variableFoot W v≤variableProfile W m K := variable_bound W v
  have hFlat := flat_bounded W (variableProfile W m K) (K-1) (rowPrice W K) m (innerProfile W m K) copied
    (variableFoot W) (rowReturn W K) (fun j => innerWindow W K j activeLabel) activeField (List.finRange m)
    (by simp only [List.length_finRange,le_refl]) (fun j _ => (hLength j).le) (fun j _ => row_work W K j)
    (fun j _ => hPayload j) (fun j _ => inner_bound W K j activeLabel) (fun j _ => List.mem_finRange j)
  have hRangeM := GeneralPaperFinRangeStorage.bounded W m copied
  have hRangeK := GeneralPaperFinRangeStorage.bounded W (K-1) copied
  have hWork := GeneralPaperStaticEnumerationPrice.variable_work W m K
  change result.2≤price W m K at hWork
  have hShape : result.2=body.2+16*(m+1)*W := rfl
  have hf := fields_bound W (natBits (callerCap W m K)) [m,K,body.2,result.2,16*(m+1)*W] (by
    intro a ha
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl
    all_goals unfold callerCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤5*(natBits (callerCap W m K)+W)+32*W at hf
  unfold window profile
  dsimp only
  dsimp only [body,result] at hf
  omega

end Blotto.GeneralPaperStaticVariableConstructionStorage
