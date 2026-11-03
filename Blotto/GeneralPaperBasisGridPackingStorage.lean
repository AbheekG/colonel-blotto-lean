import Blotto.GeneralPaperBasisGridWriteStorage

/-! Complete native grid packing: variable enumeration, original value
entries, zero-fill buffers, selected-write frames, full returned vector
and all ten parent price/return fields. Enumeration and zero-fill cursors
remain independent; source stored-table ownership stays with the caller. -/
namespace Blotto.GeneralPaperBasisGridPackingStorage
open RationalOrderCell GeneralPaperBasisStoredProducts GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint arrayProfile)
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 8192

def price (model : RationalCostModel) (W m K R : ℕ) : ℕ :=
  let d := m*(K-1)
  64*(d+1)*W+128*(d+m+1)*W+GeneralPaperBasisGridEntryStorage.price model W d R d+
    GeneralPaperBasisGridWriteStorage.price W d+16*W
def metadataCap (model : RationalCostModel) (W m K R : ℕ) : ℕ := m+K+m*(K-1)+1+3*price model W m K R+16*W
def controls {m K : ℕ} (model : RationalCostModel) (W : ℕ) (value : Variable m K → ℤ) : List ℕ :=
  let initial := GeneralPaperBasisGridPackingPrice.zero (fun w => w) W (m*(K-1))
  let vars := GeneralPaperStaticEnumerationPrice.variableRun W m K
  let entries := GeneralPaperPricedListMap.run W (GeneralPaperBasisGridEntryStorage.callback model W value) vars.1
  let inner := GeneralPaperBasisGridPackingPrice.writes W entries.1 initial.1
  let result := GeneralPaperBasisGridPackingPrice.run (fun w => w) model.rat W value
  [m*(K-1),initial.2,vars.2,entries.2,inner.2,result.2,16*W,initial.2+vars.2,initial.2+vars.2+entries.2,
    initial.2+vars.2+entries.2+inner.2]
def window {m K : ℕ} (model : RationalCostModel) (W zeroCopied enumerationCopied : ℕ) (value : Variable m K → ℤ)
    (activeField : Option (Fin m)) (activeLabel : Option (Fin (K-1))) : ℕ :=
  let initial := GeneralPaperBasisGridPackingPrice.zero (fun w => w) W (m*(K-1))
  let vars := GeneralPaperStaticEnumerationPrice.variableRun W m K
  let entries := GeneralPaperPricedListMap.run W (GeneralPaperBasisGridEntryStorage.callback model W value) vars.1
  let result := GeneralPaperBasisGridPackingPrice.run (fun w => w) model.rat W value
  GeneralPaperStaticVariableConstructionStorage.window W m K enumerationCopied activeField activeLabel+
    GeneralPaperBasisGridEntryStorage.window model W value vars.1+
    GeneralPaperNativePayloadFillStorage.window W integerBits (fun _ : Fin (m*(K-1)) => ((0:ℤ),2*W)) (fun _ => 0)
      (min zeroCopied (m*(K-1))) (Nat.min_le_right _ _)+
    GeneralPaperBasisGridWriteStorage.window W entries.1 initial.1+arrayFootprint W integerBits result.1+
    fields W (controls model W value)+256*W
def profile (model : RationalCostModel) (W m K R : ℕ) : ℕ :=
  let d := m*(K-1)
  GeneralPaperStaticVariableConstructionStorage.profile W m K+GeneralPaperBasisGridEntryStorage.profile model W m K R d+
    GeneralPaperNativePayloadFillStorage.profile W 2 d (2*W) 0+GeneralPaperBasisGridWriteStorage.profile W d R d+
    arrayProfile W d R+10*(natBits (metadataCap model W m K R)+W)+288*W

theorem bounded {m K : ℕ} (model : RationalCostModel) (W R zeroCopied enumerationCopied : ℕ) (value : Variable m K → ℤ)
    (hValues : ∀ v,integerBits (value v)≤R) (hR : 2≤R) (hW : 1≤W) (hD : binaryWordWidth (m*(K-1)+1)≤W)
    (activeField : Option (Fin m)) (activeLabel : Option (Fin (K-1))) :
    window model W zeroCopied enumerationCopied value activeField activeLabel≤profile model W m K R := by
  let d := m*(K-1)
  let initial := GeneralPaperBasisGridPackingPrice.zero (fun w => w) W d
  let vars := GeneralPaperStaticEnumerationPrice.variableRun W m K
  let entries := GeneralPaperPricedListMap.run W (GeneralPaperBasisGridEntryStorage.callback model W value) vars.1
  let inner := GeneralPaperBasisGridPackingPrice.writes W entries.1 initial.1
  let result := GeneralPaperBasisGridPackingPrice.run (fun w => w) model.rat W value
  have hVars : vars.1.length=d := by
    dsimp only [vars]
    rw [GeneralPaperStaticEnumerationPrice.variable_data,GeneralPaperStaticRayRows.variableList_length]
  have hEntries : entries.1.length=d := by dsimp only [entries]; rw [GeneralPaperPricedListMap.length,hVars]
  have hEntryWords : ∀ t∈entries.1,integerBits t.2≤R := by
    intro t ht
    change t∈(GeneralPaperPricedListMap.run W (GeneralPaperBasisGridEntryStorage.callback model W value) vars.1).1 at ht
    rw [GeneralPaperPricedListMap.data] at ht
    obtain ⟨v,_,he⟩ := List.mem_map.mp ht
    rw [←he]
    exact hValues v
  have hZero : GeneralPaperBasisGridWriteStorage.Good R initial.1 := by
    intro i
    change integerBits ((PaperIndexedArrayConstruction.run (fun w => w) W (fun _ : Fin d => ((0:ℤ),2*W))).1.read i)≤R
    rw [PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
    change integerBits (0:ℤ)≤R
    have h : integerBits (0:ℤ)=2 := by decide
    omega
  have hEnumeration := GeneralPaperStaticVariableConstructionStorage.bounded W m K enumerationCopied activeField activeLabel
  have hMap := GeneralPaperBasisGridEntryStorage.bounded model W R d value vars.1 hVars.le (fun v _ => hValues v)
  have hFill := GeneralPaperNativePayloadFillStorage.bounded W 2 (2*W) 0 integerBits (fun _ : Fin d => ((0:ℤ),2*W)) (fun _ => 0)
    (by intro i; change integerBits (0:ℤ)≤2; decide) (fun _ => le_rfl) (fun _ => le_rfl) hW hD
    (min zeroCopied d) (Nat.min_le_right _ _)
  have hWrites := GeneralPaperBasisGridWriteStorage.bounded W R d entries.1 initial.1 hZero hEntryWords hEntries.le
  have hGood := GeneralPaperBasisGridWriteStorage.returned_good W R entries.1 initial.1 hZero hEntryWords
  have hResult : arrayFootprint W integerBits result.1≤arrayProfile W d R := GeneralPaperBasisGridWriteStorage.vector_bound W R result.1 hGood
  have hZWork := GeneralPaperBasisScatterBits.zero_work W d hW hD
  change initial.2≤64*(d+1)*W at hZWork
  have hVWork := GeneralPaperStaticEnumerationPrice.variable_work W m K
  change vars.2≤128*(d+m+1)*W at hVWork
  have hEWork : entries.2≤GeneralPaperBasisGridEntryStorage.price model W d R d := by
    have h := GeneralPaperPricedListMap.work W (GeneralPaperBasisGridEntryStorage.callbackPrice model W d R)
      (GeneralPaperBasisGridEntryStorage.callback model W value) vars.1 (fun v _ => GeneralPaperBasisGridEntryStorage.callback_work model W R value v (hValues v))
    rw [hVars] at h
    exact h.trans_eq (by unfold GeneralPaperBasisGridEntryStorage.price; ring)
  have hIWork := GeneralPaperBasisGridWriteStorage.work_bound W d entries.1 initial.1 hEntries.le
  change inner.2≤GeneralPaperBasisGridWriteStorage.price W d at hIWork
  have hShape : result.2=initial.2+vars.2+entries.2+inner.2+16*W := rfl
  have hWork : result.2≤price model W m K R := by unfold price; dsimp only; dsimp only [d] at hZWork hVWork hEWork hIWork; omega
  have hf := fields_bound W (natBits (metadataCap model W m K R)) (controls model W value) (by
    intro z hz; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    change z∈[d,initial.2,vars.2,entries.2,inner.2,result.2,16*W,initial.2+vars.2,initial.2+vars.2+entries.2,initial.2+vars.2+entries.2+inner.2] at hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold metadataCap
    dsimp only [d] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W (controls model W value)≤10*(natBits (metadataCap model W m K R)+W)+32*W at hf
  unfold window profile
  dsimp only
  dsimp only [d,initial,vars,entries,result] at hEnumeration hMap hFill hWrites hResult
  omega

end Blotto.GeneralPaperBasisGridPackingStorage
