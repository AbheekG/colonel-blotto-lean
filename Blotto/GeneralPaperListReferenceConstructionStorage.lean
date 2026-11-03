import Blotto.GeneralPaperCrossingPassStorage

/-! Native list-to-reference-array construction in the paper's mutable
buffer schedule. Every reached packing keeps one buffer and a conservative
copy reservation. Recursive frames retain references and encoded native
prices, not old buffer contents or whole traversal time. -/
namespace Blotto.GeneralPaperListReferenceConstructionStorage
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def Good {α : Type*} (encode : α → ℕ) (P : ℕ) (s : List α×Array α) : Prop :=
  (∀ x∈s.1,encode x≤P) ∧ ∀ x∈s.2,encode x≤P

theorem next_good {α : Type*} (encode : α → ℕ) (P : ℕ) (s : List α×Array α) (hs : Good encode P s) :
    Good encode P (ReferenceArrayBuilder.next s) := by
  rcases s with ⟨xs,data⟩
  cases xs with
  | nil => exact hs
  | cons x rest =>
    refine ⟨fun y hy => hs.1 y (List.mem_cons_of_mem _ hy),?_⟩
    intro y hy
    rcases Array.mem_push.mp hy with hy|hy
    · exact hs.2 y hy
    · rw [hy]; exact hs.1 x List.mem_cons_self

theorem prefix_good {α : Type*} (encode : α → ℕ) (P used : ℕ) (xs : List α) (he : ∀ x∈xs,encode x≤P) :
    Good encode P (ReferenceArrayBuilder.advance used (xs,#[])) := by
  induction used with
  | zero =>
    refine ⟨he,?_⟩
    intro x hx
    obtain ⟨i,hi,_⟩ := Array.mem_iff_getElem.mp hx
    have h : i<0 := hi
    omega
  | succ used ih => exact next_good encode P _ ih

def packing {α : Type*} (W used : ℕ) (encode : α → ℕ) (xs : List α) : ℕ :=
  GeneralPaperEncodedReferenceVector.reservedFootprint W xs.length encode (ReferenceArrayBuilder.advance used (xs,#[])).2

theorem prefix_bound {α : Type*} (W P used : ℕ) (encode : α → ℕ) (xs : List α) (he : ∀ x∈xs,encode x≤P) :
    packing W used encode xs≤xs.length*(P+W)+64*W := by
  apply GeneralPaperEncodedReferenceVector.reserved_bound W P xs.length encode _
    (ReferenceArrayBuilder.every_prefix_table_size used xs)
  intro i
  exact (prefix_good encode P used xs he).2 _ (Array.getElem_mem i.isLt)

def workCap (W N : ℕ) : ℕ := 64*(N+1)*W
def metadataCap (W N : ℕ) : ℕ := N+1+3*workCap W N+50*W
def frameProfile (W N : ℕ) : ℕ := 6*(natBits (metadataCap W N)+W)+160*W

theorem step_bound (W N i : ℕ) (hi : i≤N) (hW : 1≤W) (hIndex : binaryWordWidth (N+1)≤W) :
    PaperIndexedArrayConstruction.stepWork (fun w => w) W i+8*W≤50*W := by
  have hw := (binaryWordWidth_mono (Nat.add_le_add_right hi 1)).trans hIndex
  unfold PaperIndexedArrayConstruction.stepWork
  dsimp only
  omega

theorem into_bound {α : Type*} (W N : ℕ) (xs : List α) (data : Array α)
    (hc : data.size+xs.length≤N) (hW : 1≤W) (hIndex : binaryWordWidth (N+1)≤W) :
    (PaperListReferenceArray.into (fun w => w) W xs data).2≤workCap W N := by
  have hi := PaperListReferenceArray.into_work (fun w => w) W N (50*W) xs data hc
    (fun i hi => step_bound W N i hi hW hIndex)
  have hn : xs.length≤N := by omega
  exact hi.trans ((Nat.mul_le_mul_right (50*W) hn).trans (by unfold workCap; nlinarith))

def frame {α : Type*} (W : ℕ) : List α → Array α → ℕ
  | [],data => fields W [data.size,0,(PaperListReferenceArray.into (fun w => w) W [] data).2]+128*W
  | x::rest,data =>
    let step := PaperIndexedArrayConstruction.stepWork (fun w => w) W data.size+8*W
    let child := PaperListReferenceArray.into (fun w => w) W rest (data.push x)
    let result := PaperListReferenceArray.into (fun w => w) W (x::rest) data
    fields W [data.size,(x::rest).length,step,child.2,result.2,child.2+step]+128*W

theorem frame_bound {α : Type*} (W N : ℕ) (xs : List α) (data : Array α)
    (hc : data.size+xs.length≤N) (hW : 1≤W) (hIndex : binaryWordWidth (N+1)≤W) :
    frame W xs data≤frameProfile W N := by
  cases xs with
  | nil =>
    have hf := fields_bound W (natBits (metadataCap W N)) [data.size,0,(PaperListReferenceArray.into (fun w => w) W [] data).2] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl
      all_goals unfold metadataCap; simp only [List.length_nil,Nat.add_zero] at hc; first | omega | simp only [PaperListReferenceArray.into]; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤3*(natBits (metadataCap W N)+W)+32*W at hf
    change GeneralPaperEncodedScalarStorage.fields W [data.size,0,(PaperListReferenceArray.into (fun w => w) W [] data).2]+128*W≤_
    unfold frameProfile
    omega
  | cons x rest =>
    let step := PaperIndexedArrayConstruction.stepWork (fun w => w) W data.size+8*W
    let child := PaperListReferenceArray.into (fun w => w) W rest (data.push x)
    let result := PaperListReferenceArray.into (fun w => w) W (x::rest) data
    have hStep : step≤50*W := step_bound W N data.size (by simp only [List.length_cons] at hc; omega) hW hIndex
    have hc' : (data.push x).size+rest.length≤N := by simp only [Array.size_push,List.length_cons] at hc ⊢; omega
    have hChild := into_bound W N rest (data.push x) hc' hW hIndex
    have hResult := into_bound W N (x::rest) data hc hW hIndex
    change child.2≤workCap W N at hChild
    change result.2≤workCap W N at hResult
    have hf := fields_bound W (natBits (metadataCap W N)) [data.size,(x::rest).length,step,child.2,result.2,child.2+step] (by
      intro a ha
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
    change GeneralPaperEncodedScalarStorage.fields W _≤6*(natBits (metadataCap W N)+W)+32*W at hf
    change GeneralPaperEncodedScalarStorage.fields W [data.size,(x::rest).length,step,child.2,result.2,child.2+step]+128*W≤_
    unfold frameProfile
    omega

def peak {α : Type*} (W : ℕ) : List α → Array α → ℕ
  | [],data => frame W [] data
  | x::rest,data => frame W (x::rest) data+peak W rest (data.push x)

theorem peak_bound {α : Type*} (W N : ℕ) (xs : List α) (data : Array α)
    (hc : data.size+xs.length≤N) (hW : 1≤W) (hIndex : binaryWordWidth (N+1)≤W) :
    peak W xs data≤(xs.length+1)*frameProfile W N := by
  induction xs generalizing data with
  | nil => simpa only [peak,List.length_nil,Nat.zero_add,Nat.one_mul] using frame_bound W N [] data hc hW hIndex
  | cons x rest ih =>
    have hc' : (data.push x).size+rest.length≤N := by simp only [Array.size_push,List.length_cons] at hc ⊢; omega
    exact (Nat.add_le_add (frame_bound W N (x::rest) data hc hW hIndex) (ih (data.push x) hc')).trans_eq
      (by simp only [List.length_cons]; ring)

def outer {α : Type*} (W : ℕ) (xs : List α) : ℕ :=
  let inner := PaperListReferenceArray.into (fun w => w) W xs #[]
  let result := PaperListReferenceArray.run (fun w => w) W xs
  let initial := PaperIndexedArrayConstruction.initialWork (fun w => w) W xs.length
  fields W [xs.length,inner.2,result.2,initial,(8*xs.length+8)*W,inner.2+initial]+256*W

theorem outer_bound {α : Type*} (W N : ℕ) (xs : List α) (hn : xs.length≤N)
    (hW : 1≤W) (hIndex : binaryWordWidth (N+1)≤W) :
    outer W xs≤6*(natBits (metadataCap W N)+W)+288*W := by
  let inner := PaperListReferenceArray.into (fun w => w) W xs #[]
  let result := PaperListReferenceArray.run (fun w => w) W xs
  let initial := PaperIndexedArrayConstruction.initialWork (fun w => w) W xs.length
  have hw := PaperListReferenceArray.bit_work W xs hW ((binaryWordWidth_mono (Nat.add_le_add_right hn 1)).trans hIndex)
  have hw' : result.2≤workCap W N := hw.trans (by unfold workCap; gcongr)
  have hShape : result.2=inner.2+initial+(8*xs.length+8)*W := rfl
  have hf := fields_bound W (natBits (metadataCap W N)) [xs.length,inner.2,result.2,initial,(8*xs.length+8)*W,inner.2+initial] (by
    intro a ha
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤6*(natBits (metadataCap W N)+W)+32*W at hf
  unfold outer
  change GeneralPaperEncodedScalarStorage.fields W [xs.length,inner.2,result.2,initial,(8*xs.length+8)*W,inner.2+initial]+256*W≤_
  omega

def window {α : Type*} (W used : ℕ) (encode : α → ℕ) (xs : List α) : ℕ :=
  listFootprint W encode xs+2*packing W used encode xs+peak W xs #[]+outer W xs

def profile (W P N : ℕ) : ℕ := N*(P+2*W)+32*W+2*(N*(P+W)+64*W)+
  (N+1)*frameProfile W N+6*(natBits (metadataCap W N)+W)+288*W

theorem bounded {α : Type*} (W P N used : ℕ) (encode : α → ℕ) (xs : List α)
    (hn : xs.length≤N) (he : ∀ x∈xs,encode x≤P) (hW : 1≤W) (hIndex : binaryWordWidth (N+1)≤W) :
    window W used encode xs≤profile W P N := by
  have hList := (list_bound W P encode xs he).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) _)
  have hPrefix := (prefix_bound W P used encode xs he).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) _)
  have hPeak := (peak_bound W N xs #[] (by simpa only [Array.size_empty,Nat.zero_add] using hn) hW hIndex).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right hn 1))
  have hOuter := outer_bound W N xs hn hW hIndex
  unfold window profile
  omega

end Blotto.GeneralPaperListReferenceConstructionStorage
