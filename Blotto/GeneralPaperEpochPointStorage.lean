import Blotto.GeneralPaperCellInputConstructionStorage

/-! Native breakpoint-list construction retains both array cursors, input
lists, successor-map stack, both left-copy append stacks and old/new outputs.
All lengths are erased invariants of the actual constructed lists. -/
namespace Blotto.GeneralPaperEpochPointStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem member_lt {n : ℕ} (U : ℕ) (values : FixedArrayTable n ℕ) (hv : ∀ i,values.read i<U)
    (x : ℕ) (hx : x∈values.data.toList) : x<U := by
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hx
  have hiN : i<n := by simpa only [Array.length_toList,values.size] using hi
  have hr : values.read ⟨i,hiN⟩=x := by simpa only [FixedArrayTable.read,Array.getElem_toList] using he
  rw [←hr]
  exact hv _

theorem cursor_bound {n : ℕ} (W U used : ℕ) (values : FixedArrayTable n ℕ) (hv : ∀ i,values.read i≤U) :
    GeneralPaperCataloguePointStorage.cursorFootprint W used values≤n*(natBits U+2*W)+natBits n+129*W := by
  let s := StoredArrayReferenceList.advance values.data used ⟨values.data.size,Nat.le_refl _,[]⟩
  have hm := StoredArrayReferenceList.advance_mass values.data used ⟨values.data.size,Nat.le_refl _,[]⟩
  change s.remaining+s.tail.length=values.data.size+0 at hm
  rw [values.size] at hm
  have ht := list_bound W (natBits U) natBits s.tail (by
    intro x hx
    have h := GeneralPaperEpochPointExecution.member_bound U values hv x (GeneralPaperCataloguePointStorage.cursor_members values.data used x hx)
    exact Nat.add_le_add_left (binaryWordWidth_mono h) 1)
  have hl := Nat.mul_le_mul_right (natBits U+2*W) (show s.tail.length≤n by omega)
  have hr := Nat.add_le_add_left (binaryWordWidth_mono (show s.remaining≤n by omega)) 1
  change natBits s.remaining≤natBits n at hr
  unfold GeneralPaperCataloguePointStorage.cursorFootprint fields
  dsimp only
  change (natBits s.remaining+0+1*W+32*W)+listFootprint W natBits s.tail+64*W≤_
  omega

def mapPeak (W : ℕ) : List ℕ → ℕ
  | [] => 64*W
  | x::xs => fields W [x,x+1]+128*W+mapPeak W xs

theorem map_bound (W U : ℕ) (xs : List ℕ) (hx : ∀ x∈xs,x<U) :
    mapPeak W xs≤xs.length*(2*natBits U+162*W)+64*W := by
  induction xs with
  | nil => simp only [mapPeak,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons x xs ih =>
    have h := hx x (List.mem_cons_self ..)
    have hf := fields_bound W (natBits U) [x,x+1] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl|rfl <;> unfold natBits <;> exact Nat.add_le_add_left (binaryWordWidth_mono (by omega)) 1)
    change fields W [x,x+1]≤2*(natBits U+W)+32*W at hf
    have hi := ih (fun y hy => hx y (List.mem_cons_of_mem _ hy))
    rw [mapPeak,List.length_cons]
    nlinarith only [hf,hi]

def appendPeak (W : ℕ) : List ℕ → ℕ
  | [] => 64*W
  | _::xs => 128*W+appendPeak W xs

theorem append_bound (W : ℕ) (xs : List ℕ) : appendPeak W xs=xs.length*(128*W)+64*W := by
  induction xs with
  | nil => simp only [appendPeak,List.length_nil,Nat.zero_mul,Nat.zero_add]
  | cons x xs ih => rw [appendPeak,ih,List.length_cons]; ring

def window {n m : ℕ} (model : RationalCostModel) (W usedP usedE : ℕ)
    (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ) : ℕ :=
  let p := StoredArrayReferenceList.list positions.data
  let e := StoredArrayReferenceList.list extras.data
  let successors := GeneralPaperPricedListMap.run W (GeneralPaperEpochPointExecution.successor model.rat W) p
  let joined := GeneralPaperPricedListAppend.run W p successors.1
  let all := GeneralPaperPricedListAppend.run W joined.1 e
  GeneralPaperEncodedNatArray.footprint W positions+GeneralPaperEncodedNatArray.footprint W extras+
    GeneralPaperCataloguePointStorage.cursorFootprint W usedP positions+GeneralPaperCataloguePointStorage.cursorFootprint W usedE extras+
    listFootprint W natBits p+listFootprint W natBits e+2*listFootprint W natBits successors.1+
    2*listFootprint W natBits joined.1+2*listFootprint W natBits all.1+
    mapPeak W p+appendPeak W p+appendPeak W joined.1+fields W [n,m]+
    (GeneralPaperEpochPointExecution.run true (fun w => w) model.rat W positions extras).2+256*W

def profile (model : RationalCostModel) (W U n m : ℕ) : ℕ :=
  (n*(natBits U+W)+32*W)+(m*(natBits U+W)+32*W)+
    (n*(natBits U+2*W)+natBits n+129*W)+(m*(natBits U+2*W)+natBits m+129*W)+
    (n*(natBits U+2*W)+32*W)+(m*(natBits U+2*W)+32*W)+2*(n*(natBits U+2*W)+32*W)+
    2*((2*n)*(natBits U+2*W)+32*W)+2*((2*n+m)*(natBits U+2*W)+32*W)+
    (n*(2*natBits U+162*W)+64*W)+(n*(128*W)+64*W)+((2*n)*(128*W)+64*W)+fields W [n,m]+
    GeneralPaperEpochPointPrice.profile model.rat W n m U+256*W

theorem bounded {n m : ℕ} (model : RationalCostModel) (W U usedP usedE : ℕ)
    (positions : FixedArrayTable n ℕ) (extras : FixedArrayTable m ℕ)
    (hp : ∀ i,positions.read i<U) (he : ∀ i,extras.read i≤U) :
    window model W usedP usedE positions extras≤profile model W U n m := by
  let p := StoredArrayReferenceList.list positions.data
  let e := StoredArrayReferenceList.list extras.data
  let successors := GeneralPaperPricedListMap.run W (GeneralPaperEpochPointExecution.successor model.rat W) p
  let joined := GeneralPaperPricedListAppend.run W p successors.1
  let all := GeneralPaperPricedListAppend.run W joined.1 e
  have hplen : p.length=n := by simp only [p,StoredArrayReferenceList.list_data,Array.length_toList,positions.size]
  have helen : e.length=m := by simp only [e,StoredArrayReferenceList.list_data,Array.length_toList,extras.size]
  have hslen : successors.1.length=n := by rw [GeneralPaperPricedListMap.length,hplen]
  have hjlen : joined.1.length=2*n := by rw [GeneralPaperPricedListAppend.data,List.length_append,hplen,hslen]; omega
  have halen : all.1.length=2*n+m := by rw [GeneralPaperPricedListAppend.data,List.length_append,hjlen,helen]
  have hpval : ∀ x∈p,x<U := fun x hx => member_lt U positions hp x (by simpa only [p,StoredArrayReferenceList.list_data] using hx)
  have heval : ∀ x∈e,x≤U := fun x hx => GeneralPaperEpochPointExecution.member_bound U extras he x (by simpa only [e,StoredArrayReferenceList.list_data] using hx)
  have hsval : ∀ x∈successors.1,x≤U := by
    intro x hx
    rw [GeneralPaperPricedListMap.data] at hx
    obtain ⟨y,hy,hxy⟩ := List.mem_map.mp hx
    have hyU := hpval y hy
    change y+1=x at hxy
    omega
  have hjval : ∀ x∈joined.1,x≤U := by
    intro x hx
    rw [GeneralPaperPricedListAppend.data] at hx
    rcases List.mem_append.mp hx with hx|hx
    · exact (hpval x hx).le
    · exact hsval x hx
  have haval : ∀ x∈all.1,x≤U := by
    intro x hx
    rw [GeneralPaperPricedListAppend.data] at hx
    rcases List.mem_append.mp hx with hx|hx
    · exact hjval x hx
    · exact heval x hx
  have arrP := GeneralPaperEncodedNatArray.bounded W (natBits U) positions (fun i => Nat.add_le_add_left (binaryWordWidth_mono (hp i).le) 1)
  have arrE := GeneralPaperEncodedNatArray.bounded W (natBits U) extras (fun i => Nat.add_le_add_left (binaryWordWidth_mono (he i)) 1)
  have curP := cursor_bound W U usedP positions (fun i => (hp i).le)
  have curE := cursor_bound W U usedE extras he
  have listP := list_bound W (natBits U) natBits p (fun x hx => Nat.add_le_add_left (binaryWordWidth_mono (hpval x hx).le) 1)
  have listE := list_bound W (natBits U) natBits e (fun x hx => Nat.add_le_add_left (binaryWordWidth_mono (heval x hx)) 1)
  have listS := list_bound W (natBits U) natBits successors.1 (fun x hx => Nat.add_le_add_left (binaryWordWidth_mono (hsval x hx)) 1)
  have listJ := list_bound W (natBits U) natBits joined.1 (fun x hx => Nat.add_le_add_left (binaryWordWidth_mono (hjval x hx)) 1)
  have listA := list_bound W (natBits U) natBits all.1 (fun x hx => Nat.add_le_add_left (binaryWordWidth_mono (haval x hx)) 1)
  rw [hplen] at listP
  rw [helen] at listE
  rw [hslen] at listS
  rw [hjlen] at listJ
  rw [halen] at listA
  have hmap := map_bound W U p hpval
  rw [hplen] at hmap
  have happ := append_bound W p
  have happ' := append_bound W joined.1
  rw [hplen] at happ
  rw [hjlen] at happ'
  have hprice := GeneralPaperEpochPointPrice.bit_work model.rat model.monotone W U positions extras hp
  unfold window profile
  dsimp only
  dsimp only [p,e,successors,joined,all] at listP listE listS listJ listA hmap happ happ'
  omega

end Blotto.GeneralPaperEpochPointStorage
