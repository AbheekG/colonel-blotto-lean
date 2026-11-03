import Blotto.GeneralPaperQuantizedColumnParentStorage

/-! Literal native quantization field/matrix callers. Full source rows,
returned columns, outer fill buffers/frames and one active field parent
coexist. Complete column parents retain the actual materialized values and
stable order. Native child work contributes only encoded parent metadata. -/
namespace Blotto.GeneralPaperQuantizedMatrixParentStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEnclosingSourceOwners
set_option autoImplicit false
set_option maxHeartbeats 15000000
set_option maxRecDepth 16384

def fieldPrice (model : RationalCostModel) (W T K B R : ℕ) : ℕ :=
  GeneralPaperColumnInputStorage.price W T+GeneralPaperQuantizedColumnParentStorage.price model W T K B R+32*W
def callbackPrice (model : RationalCostModel) (W T K B R : ℕ) : ℕ := fieldPrice model W T K B R+64*W
def price (model : RationalCostModel) (W T m K B R : ℕ) : ℕ :=
  GeneralPaperNativePayloadFillStorage.workCap W m (callbackPrice model W T K B R)
def fieldCap (model : RationalCostModel) (W T K B R : ℕ) : ℕ := fieldPrice model W T K B R+64*W+1
def metadataCap (model : RationalCostModel) (W T m K B R : ℕ) : ℕ := T+m+K+B+price model W T m K B R+64*W+1
def fieldWindow {K B m : ℕ} (model : RationalCostModel) (W : ℕ) (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) (j : Fin m) : ℕ :=
  let input := GeneralPaperNativeQuantizedMatrix.columnInput (fun w => w) W rows j
  let column := GeneralPaperNativeQuantizedColumn.run model.rat (fun w => w) W hK hB input.1
  let result := GeneralPaperNativeQuantizedMatrix.field model.rat (fun w => w) W hK hB rows j
  GeneralPaperQuantizedColumnParentStorage.window model W hK hB input.1+
    fields W [input.2,column.2,result.2,input.2+column.2,32*W]+64*W
def fieldProfile (model : RationalCostModel) (W T K B R : ℕ) : ℕ :=
  GeneralPaperQuantizedColumnParentStorage.profile model W T K B R+5*(natBits (fieldCap model W T K B R)+W)+96*W
def window {K B m : ℕ} (model : RationalCostModel) (W : ℕ) (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) (outer : ℕ) (ho : outer≤m) (active : Option (Fin m)) : ℕ :=
  let result := GeneralPaperNativeQuantizedMatrix.run model.rat (fun w => w) W hK hB rows
  let callback := fun j => let col := GeneralPaperNativeQuantizedMatrix.field model.rat (fun w => w) W hK hB rows j; (col.1,col.2+64*W)
  rowsFoot W rows+columnsFoot W result.1+
    GeneralPaperNativePayloadFillStorage.window W (columnFoot W) callback (fun _ => 0) outer ho+
    (match active with | none => 0 | some j => fieldWindow model W hK hB rows j)+
    fields W [K*B,m,K,B,result.2,64*W]+128*W
def profile (model : RationalCostModel) (W T m K B R : ℕ) : ℕ :=
  rowsProfile W T m R+columnsProfile W T m K R+
    GeneralPaperNativePayloadFillStorage.profile W (columnProfile W T K R) m (callbackPrice model W T K B R) 0+
    fieldProfile model W T K B R+6*(natBits (metadataCap model W T m K B R)+W)+160*W

theorem input_words {T m : ℕ} (W R : ℕ) (rows : FixedArrayTable T (FixedArrayTable m ℚ))
    (hv : ∀ i j,rationalWordWidth ((rows.read i).read j)≤R) (j : Fin m) :
    ∀ i,rationalWordWidth ((GeneralPaperNativeQuantizedMatrix.columnInput (fun w => w) W rows j).1.read i)≤R := by
  intro i
  rw [GeneralPaperNativeQuantizedMatrix.input_data,GeneralPaperRowQuantizer.columnInput,FixedArrayTable.read_ofFn]
  exact hv i j

theorem field_anchors {K B m : ℕ} (model : RationalCostModel) (W R : ℕ) (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) (hR : 3≤R)
    (hv : ∀ i j,rationalWordWidth ((rows.read i).read j)≤R) (j : Fin m) :
    ∀ l,rationalWordWidth ((GeneralPaperNativeQuantizedMatrix.field model.rat (fun w => w) W hK hB rows j).1.anchors.read l)≤R :=
  GeneralPaperQuantizedColumnParentStorage.anchors_word model W R hK hB _ hR (input_words W R rows hv j)

theorem returned_bound {K B m : ℕ} (model : RationalCostModel) (W R : ℕ) (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) (hR : 3≤R) (hv : ∀ i j,rationalWordWidth ((rows.read i).read j)≤R) :
    columnsFoot W (GeneralPaperNativeQuantizedMatrix.run model.rat (fun w => w) W hK hB rows).1≤columnsProfile W (K*B) m K R := by
  apply columns_bound W R
  intro j l
  unfold GeneralPaperNativeQuantizedMatrix.run
  rw [PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  exact field_anchors model W R hK hB rows hR hv j l

theorem field_work {K B m : ℕ} (model : RationalCostModel) (W R : ℕ) (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) (hv : ∀ i j,rationalWordWidth ((rows.read i).read j)≤R)
    (hW : 1≤W) (hIndex : binaryWordWidth (K*B+K*B+1)≤W) (hLabels : binaryWordWidth (K+1)≤W) (j : Fin m) :
    (GeneralPaperNativeQuantizedMatrix.field model.rat (fun w => w) W hK hB rows j).2≤fieldPrice model W (K*B) K B R := by
  have hT : binaryWordWidth (K*B+1)≤W := (binaryWordWidth_mono (by omega)).trans hIndex
  have hInput := GeneralPaperColumnInputStorage.work W rows j hW hT
  have hColumn := GeneralPaperQuantizedColumnParentStorage.work model W R hK hB _ (input_words W R rows hv j) hW hIndex hLabels
  unfold GeneralPaperNativeQuantizedMatrix.field fieldPrice
  dsimp only
  omega

theorem field_bound {K B m : ℕ} (model : RationalCostModel) (W R : ℕ) (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) (hR : 3≤R) (hv : ∀ i j,rationalWordWidth ((rows.read i).read j)≤R)
    (hW : 1≤W) (hIndex : binaryWordWidth (K*B+K*B+1)≤W) (hLabels : binaryWordWidth (K+1)≤W) (j : Fin m) :
    fieldWindow model W hK hB rows j≤fieldProfile model W (K*B) K B R := by
  let input := GeneralPaperNativeQuantizedMatrix.columnInput (fun w => w) W rows j
  let column := GeneralPaperNativeQuantizedColumn.run model.rat (fun w => w) W hK hB input.1
  let result := GeneralPaperNativeQuantizedMatrix.field model.rat (fun w => w) W hK hB rows j
  have hColumn := GeneralPaperQuantizedColumnParentStorage.bounded model W R hK hB input.1 hR (input_words W R rows hv j) hW hIndex hLabels
  have hWork := field_work model W R hK hB rows hv hW hIndex hLabels j
  change result.2≤fieldPrice model W (K*B) K B R at hWork
  have hShape : result.2=input.2+column.2+32*W := rfl
  have hf := fields_bound W (natBits (fieldCap model W (K*B) K B R))
    [input.2,column.2,result.2,input.2+column.2,32*W] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl
      all_goals unfold fieldCap; omega)
  change fields W _≤5*(natBits (fieldCap model W (K*B) K B R)+W)+32*W at hf
  change GeneralPaperQuantizedColumnParentStorage.window model W hK hB input.1+
    fields W [input.2,column.2,result.2,input.2+column.2,32*W]+64*W≤_
  unfold fieldProfile
  omega

theorem work {K B m : ℕ} (model : RationalCostModel) (W R : ℕ) (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) (hv : ∀ i j,rationalWordWidth ((rows.read i).read j)≤R)
    (hW : 1≤W) (hIndex : binaryWordWidth (K*B+K*B+1)≤W) (hLabels : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W) :
    (GeneralPaperNativeQuantizedMatrix.run model.rat (fun w => w) W hK hB rows).2≤price model W (K*B) m K B R :=
  GeneralPaperNativePayloadFillStorage.prefix_work W (callbackPrice model W (K*B) K B R)
    (fun j => let col := GeneralPaperNativeQuantizedMatrix.field model.rat (fun w => w) W hK hB rows j; (col.1,col.2+64*W))
    (fun j => Nat.add_le_add_right (field_work model W R hK hB rows hv hW hIndex hLabels j) _) hW hM m le_rfl

theorem bounded {K B m : ℕ} (model : RationalCostModel) (W R : ℕ) (hK : 0<K) (hB : 0<B)
    (rows : FixedArrayTable (K*B) (FixedArrayTable m ℚ)) (hR : 3≤R) (hv : ∀ i j,rationalWordWidth ((rows.read i).read j)≤R)
    (hW : 1≤W) (hIndex : binaryWordWidth (K*B+K*B+1)≤W) (hLabels : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (outer : ℕ) (ho : outer≤m) (active : Option (Fin m)) : window model W hK hB rows outer ho active≤profile model W (K*B) m K B R := by
  let result := GeneralPaperNativeQuantizedMatrix.run model.rat (fun w => w) W hK hB rows
  let callback := fun j => let col := GeneralPaperNativeQuantizedMatrix.field model.rat (fun w => w) W hK hB rows j; (col.1,col.2+64*W)
  have hRows := rows_bound W R rows hv
  have hReturned := columns_bound W R result.1 (by
    intro j l
    change rationalWordWidth (((PaperIndexedArrayConstruction.run (fun w => w) W callback).1.read j).anchors.read l)≤R
    rw [PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
    exact field_anchors model W R hK hB rows hR hv j l)
  have hPayload (j : Fin m) : columnFoot W (callback j).1≤columnProfile W (K*B) K R :=
    column_bound W R _ (field_anchors model W R hK hB rows hR hv j)
  have hFill := GeneralPaperNativePayloadFillStorage.bounded W (columnProfile W (K*B) K R) (callbackPrice model W (K*B) K B R) 0
    (columnFoot W) callback (fun _ => 0) hPayload
    (fun j => Nat.add_le_add_right (field_work model W R hK hB rows hv hW hIndex hLabels j) _) (fun _ => le_rfl) hW hM outer ho
  have hActive : (match active with | none => 0 | some j => fieldWindow model W hK hB rows j)≤fieldProfile model W (K*B) K B R := by
    cases active with
    | none => exact Nat.zero_le _
    | some j => exact field_bound model W R hK hB rows hR hv hW hIndex hLabels j
  have hWork := work model W R hK hB rows hv hW hIndex hLabels hM
  change result.2≤price model W (K*B) m K B R at hWork
  have hf := fields_bound W (natBits (metadataCap model W (K*B) m K B R)) [K*B,m,K,B,result.2,64*W] (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals unfold metadataCap; omega)
  change fields W _≤6*(natBits (metadataCap model W (K*B) m K B R)+W)+32*W at hf
  change rowsFoot W rows+columnsFoot W result.1+
    GeneralPaperNativePayloadFillStorage.window W (columnFoot W) callback (fun _ => 0) outer ho+_+
    fields W [K*B,m,K,B,result.2,64*W]+128*W≤_
  unfold profile
  omega

theorem price_mono (model : RationalCostModel) (W T m K b B R : ℕ) (hb : b≤B) :
    price model W T m K b R≤price model W T m K B R := by
  have h := GeneralPaperQuantizedColumnParentStorage.price_mono model W T K b B R hb
  unfold price callbackPrice fieldPrice GeneralPaperNativePayloadFillStorage.workCap
  gcongr

theorem profile_mono (model : RationalCostModel) (W T m K b B R : ℕ) (hb : b≤B) :
    profile model W T m K b R≤profile model W T m K B R := by
  have hC := GeneralPaperQuantizedColumnParentStorage.price_mono model W T K b B R hb
  have hCP := GeneralPaperQuantizedColumnParentStorage.profile_mono model W T K b B R hb
  have hP := price_mono model W T m K b B R hb
  have hF : fieldProfile model W T K b R≤fieldProfile model W T K B R := by
    unfold fieldProfile fieldCap fieldPrice natBits
    gcongr
  have hFill : GeneralPaperNativePayloadFillStorage.profile W (columnProfile W T K R) m (callbackPrice model W T K b R) 0≤
      GeneralPaperNativePayloadFillStorage.profile W (columnProfile W T K R) m (callbackPrice model W T K B R) 0 := by
    unfold GeneralPaperNativePayloadFillStorage.profile GeneralPaperNativePayloadFillStorage.frameProfile
      GeneralPaperNativePayloadFillStorage.metadataCap GeneralPaperNativePayloadFillStorage.workCap callbackPrice fieldPrice natBits
    gcongr
  unfold profile metadataCap natBits
  gcongr

end Blotto.GeneralPaperQuantizedMatrixParentStorage
