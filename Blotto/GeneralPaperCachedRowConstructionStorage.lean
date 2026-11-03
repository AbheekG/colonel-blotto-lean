import Blotto.GeneralPaperSortedReferenceConstructionStorage

/-! Native representative extraction, one sorted row, and the complete
stored sorted-row table. Columns retain anchor payloads; table entries
and indexed-fill frames own arrays of references. Only an active sort
window carries its rational operand payloads. -/
namespace Blotto.GeneralPaperCachedRowConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open GeneralPaperCachedCircleRows
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384

def representativeCallback {T h R K : ℕ} (W : ℕ)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T) (a : Fin R) : ℚ×ℕ :=
  let column := columns.read (Fin.natAdd h a)
  (column.anchors.read (column.labels.read i),
    GeneralPaperNaturalPrimitivePrice.binary (fun w => w) (fun a b => a+b) h a.val+128*W)

def representativeScalar {T h R K : ℕ} (W : ℕ)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T) (a : Fin R) : ℕ :=
  let label := (columns.read (Fin.natAdd h a)).labels.read i
  let add := GeneralPaperNaturalPrimitivePrice.binary (fun w => w) (fun a b => a+b) h a.val
  add+fields W [h,R,T,K,i.val,a.val,h+a.val,label.val,add,128*W,(representativeCallback W columns i a).2]+128*W

def representativeScalarProfile (W T h R K : ℕ) : ℕ :=
  4*W+11*(natBits (h+R+T+K+132*W+1)+W)+160*W

theorem representative_price {T h R K : ℕ} (W : ℕ)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T) (a : Fin R)
    (hW : 1≤W) (hIndex : binaryWordWidth (h+R+1)≤W) :
    (representativeCallback W columns i a).2≤132*W := by
  have ha := a.isLt.le
  have hp := GeneralPaperNaturalPrimitivePrice.binary_le (fun w => w) (fun _ _ hx => hx)
    (fun a b => a+b) h a.val (h+R) (by omega) (by omega) (by omega)
  have hb := binaryWordWidth_mono (show h+R≤h+R+1 by omega)
  unfold representativeCallback
  dsimp only
  omega

theorem representative_scalar_bound {T h R K : ℕ} (W : ℕ)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T) (a : Fin R)
    (hW : 1≤W) (hIndex : binaryWordWidth (h+R+1)≤W) :
    representativeScalar W columns i a≤representativeScalarProfile W T h R K := by
  let label := (columns.read (Fin.natAdd h a)).labels.read i
  let add := GeneralPaperNaturalPrimitivePrice.binary (fun w => w) (fun a b => a+b) h a.val
  have hp := representative_price W columns i a hW hIndex
  have hShape : (representativeCallback W columns i a).2=add+128*W := rfl
  have ha := a.isLt.le
  have hi := i.isLt.le
  have hl := label.isLt.le
  have hf := fields_bound W (natBits (h+R+T+K+132*W+1))
    [h,R,T,K,i.val,a.val,h+a.val,label.val,add,128*W,(representativeCallback W columns i a).2] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤11*(natBits (h+R+T+K+132*W+1)+W)+32*W at hf
  change add+fields W [h,R,T,K,i.val,a.val,h+a.val,label.val,add,128*W,(representativeCallback W columns i a).2]+128*W≤_
  unfold representativeScalarProfile
  omega

def rowPrice (model : RationalCostModel) (W R H : ℕ) : ℕ :=
  GeneralPaperNativePayloadFillStorage.workCap W R (132*W)+
    GeneralPaperSortedReferenceConstructionStorage.price model W R H+64*W
def rowCap (model : RationalCostModel) (W T h R K H : ℕ) : ℕ :=
  T+h+R+K+rowPrice model W R H+64*W+1

def rowWindow {T h R K : ℕ} (model : RationalCostModel) (W : ℕ)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T)
    (count : ℕ) (hc : count≤R) (used copied : ℕ) (active : Option (Fin R×Fin R)) : ℕ :=
  let input := representatives (fun w => w) W columns i
  let sorted := GeneralPaperNativeSortedRows.one model.rat (fun w => w) W input.1
  let made := sortedRow model.rat (fun w => w) W columns i
  GeneralPaperNativePayloadFillStorage.window W (fun _ : ℚ => 0) (representativeCallback W columns i)
    (representativeScalar W columns i) count hc+
    GeneralPaperSortedReferenceConstructionStorage.window model W input.1 used copied count hc active+
    fields W [input.2,sorted.2,input.2+sorted.2,64*W,made.2]+128*W

def rowProfile (model : RationalCostModel) (W T h R K H : ℕ) : ℕ :=
  GeneralPaperNativePayloadFillStorage.profile W 0 R (132*W) (representativeScalarProfile W T h R K)+
    GeneralPaperSortedReferenceConstructionStorage.profile model W R H+
    5*(natBits (rowCap model W T h R K H)+W)+160*W

theorem input_words {T h R K : ℕ} (W H : ℕ)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T)
    (hv : ∀ j l,rationalWordWidth ((columns.read j).anchors.read l)≤H) :
    ∀ a,rationalWordWidth ((representatives (fun w => w) W columns i).1.read a)≤H := by
  intro a
  rw [representatives_data,FixedArrayTable.read_ofFn]
  exact hv _ _

theorem row_work {T h R K : ℕ} (model : RationalCostModel) (W H : ℕ)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T)
    (hv : ∀ j l,rationalWordWidth ((columns.read j).anchors.read l)≤H)
    (hW : 1≤W) (hIndex : binaryWordWidth (h+R+1)≤W) :
    (sortedRow model.rat (fun w => w) W columns i).2≤rowPrice model W R H := by
  have hr : binaryWordWidth (R+1)≤W := (binaryWordWidth_mono (by omega : R+1≤h+R+1)).trans hIndex
  have hFill := GeneralPaperNativePayloadFillStorage.prefix_work W (132*W) (representativeCallback W columns i)
    (fun a => representative_price W columns i a hW hIndex) hW hr R le_rfl
  change (representatives (fun w => w) W columns i).2≤GeneralPaperNativePayloadFillStorage.workCap W R (132*W) at hFill
  have hSort := GeneralPaperSortedReferenceConstructionStorage.work model W H
    (representatives (fun w => w) W columns i).1 (input_words W H columns i hv) hW hr
  unfold sortedRow rowPrice
  dsimp only
  omega

theorem row_bounded {T h R K : ℕ} (model : RationalCostModel) (W H : ℕ)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T)
    (hv : ∀ j l,rationalWordWidth ((columns.read j).anchors.read l)≤H)
    (hW : 1≤W) (hIndex : binaryWordWidth (h+R+1)≤W)
    (count : ℕ) (hc : count≤R) (used copied : ℕ) (active : Option (Fin R×Fin R)) :
    rowWindow model W columns i count hc used copied active≤rowProfile model W T h R K H := by
  have hr : binaryWordWidth (R+1)≤W := (binaryWordWidth_mono (by omega : R+1≤h+R+1)).trans hIndex
  have hFill := GeneralPaperNativePayloadFillStorage.bounded W 0 (132*W) (representativeScalarProfile W T h R K)
    (fun _ : ℚ => 0) (representativeCallback W columns i) (representativeScalar W columns i)
    (fun _ => le_rfl) (fun a => representative_price W columns i a hW hIndex)
    (fun a => representative_scalar_bound W columns i a hW hIndex) hW hr count hc
  have hSort := GeneralPaperSortedReferenceConstructionStorage.bounded model W H
    (representatives (fun w => w) W columns i).1 (input_words W H columns i hv) hW hr used copied count hc active
  have hw := row_work model W H columns i hv hW hIndex
  have hShape : (sortedRow model.rat (fun w => w) W columns i).2=
    (representatives (fun w => w) W columns i).2+
    (GeneralPaperNativeSortedRows.one model.rat (fun w => w) W (representatives (fun w => w) W columns i).1).2+64*W := rfl
  have hf := fields_bound W (natBits (rowCap model W T h R K H))
    [(representatives (fun w => w) W columns i).2,
      (GeneralPaperNativeSortedRows.one model.rat (fun w => w) W (representatives (fun w => w) W columns i).1).2,
      (representatives (fun w => w) W columns i).2+
      (GeneralPaperNativeSortedRows.one model.rat (fun w => w) W (representatives (fun w => w) W columns i).1).2,
      64*W,(sortedRow model.rat (fun w => w) W columns i).2] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold rowCap
      rcases hz with rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤5*(natBits (rowCap model W T h R K H)+W)+32*W at hf
  unfold rowWindow rowProfile
  dsimp only
  omega

def tableCallback {T h R K : ℕ} (model : RationalCostModel) (W : ℕ)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T) : FixedArrayTable R ℚ×ℕ :=
  let row := sortedRow model.rat (fun w => w) W columns i
  (row.1,row.2+64*W)

def tableScalar {T h R K : ℕ} (model : RationalCostModel) (W : ℕ)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T) : ℕ :=
  fields W [i.val,(sortedRow model.rat (fun w => w) W columns i).2,64*W,(tableCallback model W columns i).2]+128*W

def tableScalarProfile (model : RationalCostModel) (W T h R K H : ℕ) : ℕ :=
  4*(natBits (rowCap model W T h R K H)+W)+160*W

theorem table_scalar_bound {T h R K : ℕ} (model : RationalCostModel) (W H : ℕ)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T)
    (hv : ∀ j l,rationalWordWidth ((columns.read j).anchors.read l)≤H)
    (hW : 1≤W) (hIndex : binaryWordWidth (h+R+1)≤W) :
    tableScalar model W columns i≤tableScalarProfile model W T h R K H := by
  have hw := row_work model W H columns i hv hW hIndex
  have hi := i.isLt.le
  have hf := fields_bound W (natBits (rowCap model W T h R K H))
    [i.val,(sortedRow model.rat (fun w => w) W columns i).2,64*W,(tableCallback model W columns i).2] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      simp only [tableCallback] at hz
      unfold rowCap
      rcases hz with rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤4*(natBits (rowCap model W T h R K H)+W)+32*W at hf
  unfold tableScalar tableScalarProfile
  omega

def price (model : RationalCostModel) (W T R H : ℕ) : ℕ :=
  GeneralPaperNativePayloadFillStorage.workCap W T (rowPrice model W R H+64*W)+64*W
def cap (model : RationalCostModel) (W T R H : ℕ) : ℕ := T+price model W T R H+64*W+1

def window {T h R K : ℕ} (model : RationalCostModel) (W : ℕ)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K))
    (rows count : ℕ) (hRows : rows≤T) (hc : count≤R) (used copied : ℕ) (active : Option (Fin R×Fin R)) : ℕ :=
  let sorted := sortedRows model.rat (fun w => w) W columns
  let made := prepare model.rat (fun w => w) W columns
  GeneralPaperEnclosingSourceOwners.columnsFoot W columns+
    GeneralPaperNativePayloadFillStorage.window W (arrayFootprint W (fun _ : ℚ => 0))
      (tableCallback model W columns)
      (fun i => rowWindow model W columns i count hc used copied active+tableScalar model W columns i) rows hRows+
    fields W [T,sorted.2,64*W,made.2]+128*W

def profile (model : RationalCostModel) (W T h R K H : ℕ) : ℕ :=
  GeneralPaperEnclosingSourceOwners.columnsProfile W T (h+R) K H+
    GeneralPaperNativePayloadFillStorage.profile W (arrayProfile W R 0) T (rowPrice model W R H+64*W)
      (rowProfile model W T h R K H+tableScalarProfile model W T h R K H)+
    4*(natBits (cap model W T R H)+W)+160*W

theorem work {T h R K : ℕ} (model : RationalCostModel) (W H : ℕ)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K))
    (hv : ∀ j l,rationalWordWidth ((columns.read j).anchors.read l)≤H)
    (hW : 1≤W) (hIndex : binaryWordWidth (h+R+1)≤W) (hRows : binaryWordWidth (T+1)≤W) :
    (prepare model.rat (fun w => w) W columns).2≤price model W T R H := by
  have hf := GeneralPaperNativePayloadFillStorage.prefix_work W (rowPrice model W R H+64*W)
    (tableCallback model W columns) (fun i => Nat.add_le_add_right (row_work model W H columns i hv hW hIndex) _)
    hW hRows T le_rfl
  change (sortedRows model.rat (fun w => w) W columns).2≤
    GeneralPaperNativePayloadFillStorage.workCap W T (rowPrice model W R H+64*W) at hf
  unfold prepare price
  dsimp only
  omega

theorem bounded {T h R K : ℕ} (model : RationalCostModel) (W H : ℕ)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K))
    (hv : ∀ j l,rationalWordWidth ((columns.read j).anchors.read l)≤H)
    (hW : 1≤W) (hIndex : binaryWordWidth (h+R+1)≤W) (hRowIndex : binaryWordWidth (T+1)≤W)
    (rows count : ℕ) (hRows : rows≤T) (hc : count≤R) (used copied : ℕ) (active : Option (Fin R×Fin R)) :
    window model W columns rows count hRows hc used copied active≤profile model W T h R K H := by
  have hColumns := GeneralPaperEnclosingSourceOwners.columns_bound W H columns hv
  have hFill := GeneralPaperNativePayloadFillStorage.bounded W (arrayProfile W R 0) (rowPrice model W R H+64*W)
    (rowProfile model W T h R K H+tableScalarProfile model W T h R K H)
    (arrayFootprint W (fun _ : ℚ => 0)) (tableCallback model W columns)
    (fun i => rowWindow model W columns i count hc used copied active+tableScalar model W columns i)
    (fun _ => array_bound W 0 (fun _ : ℚ => 0) _ (fun _ => le_rfl))
    (fun i => Nat.add_le_add_right (row_work model W H columns i hv hW hIndex) _)
    (fun i => Nat.add_le_add (row_bounded model W H columns i hv hW hIndex count hc used copied active)
      (table_scalar_bound model W H columns i hv hW hIndex)) hW hRowIndex rows hRows
  have hw := work model W H columns hv hW hIndex hRowIndex
  have hShape : (prepare model.rat (fun w => w) W columns).2=(sortedRows model.rat (fun w => w) W columns).2+64*W := rfl
  have hf := fields_bound W (natBits (cap model W T R H))
    [T,(sortedRows model.rat (fun w => w) W columns).2,64*W,(prepare model.rat (fun w => w) W columns).2] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold cap
      rcases hz with rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤4*(natBits (cap model W T R H)+W)+32*W at hf
  unfold window profile
  dsimp only
  omega

end Blotto.GeneralPaperCachedRowConstructionStorage
