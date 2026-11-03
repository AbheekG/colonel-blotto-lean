import Blotto.GeneralPaperRationalArrayScaleStorage

/-! Literal native dictionary normalization. Original and returned columns,
shared full label arrays, nested anchor constructor buffers/frames, one
reciprocal scratch and native field/parent counters coexist. Active field
and outer/inner cursors are independent erased observers. -/
namespace Blotto.GeneralPaperDictionaryNormalizationStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEnclosingSourceOwners
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 16384

def field {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (c : ℚ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) (j : Fin m) : GeneralPaperQuantizedColumn.Column T K×ℕ :=
  let old := columns.read j
  let anchors := GeneralPaperRationalOutputScale.run model.rat (fun w => w) W c old.anchors
  (⟨old.labels,anchors.1⟩,anchors.2+96*W)
def fieldPrice (model : RationalCostModel) (W K R : ℕ) : ℕ := GeneralPaperRationalArrayScaleStorage.price model W K R+96*W
def fieldCap (model : RationalCostModel) (W K R : ℕ) : ℕ := fieldPrice model W K R+1
def scalePrice (model : RationalCostModel) (W m K R : ℕ) : ℕ :=
  GeneralPaperNativePayloadFillStorage.workCap W m (fieldPrice model W K R)
def price (model : RationalCostModel) (W m K R : ℕ) : ℕ := scalePrice model W m K R+2*model.rat R+32*W
def metadataCap (model : RationalCostModel) (W m K R : ℕ) : ℕ := price model W m K R+1
def fieldWindow {T K : ℕ} (model : RationalCostModel) (W : ℕ) (c : ℚ) (old : GeneralPaperQuantizedColumn.Column T K)
    (inner : ℕ) (hi : inner≤K) : ℕ :=
  let anchors := GeneralPaperRationalOutputScale.run model.rat (fun w => w) W c old.anchors
  GeneralPaperRationalArrayScaleStorage.window model W c old.anchors inner hi+
    fields W [anchors.2,96*W,anchors.2+96*W]+64*W
def fieldProfile (model : RationalCostModel) (W K R : ℕ) : ℕ := GeneralPaperRationalArrayScaleStorage.profile model W K R+
  3*(natBits (fieldCap model W K R)+W)+96*W
def controls {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (budget : ℚ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K)) : List ℕ :=
  let scaled := GeneralPaperNativeDictionaryNormalize.scale model.rat (fun w => w) W budget⁻¹ columns
  let inverse := GeneralPaperRationalPrimitivePrice.unary model.rat (fun x => x⁻¹) budget
  let result := GeneralPaperNativeDictionaryNormalize.run model.rat (fun w => w) W budget columns
  [scaled.2,inverse,result.2,scaled.2+inverse,32*W]
def window {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (budget : ℚ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (outer : ℕ) (ho : outer≤m) (inner : ℕ) (hi : inner≤K) (active : Option (Fin m)) : ℕ :=
  let result := GeneralPaperNativeDictionaryNormalize.run model.rat (fun w => w) W budget columns
  columnsFoot W columns+columnsFoot W result.1+
    GeneralPaperNativePayloadFillStorage.window W (columnFoot W) (field model W budget⁻¹ columns) (fun _ => 0) outer ho+
    (match active with | none => 0 | some j => fieldWindow model W budget⁻¹ (columns.read j) inner hi)+
    rationalWordWidth budget+rationalWordWidth budget⁻¹+
    GeneralPaperRationalPrimitivePrice.unary model.rat (fun x => x⁻¹) budget+
    fields W (controls model W budget columns)+128*W
def profile (model : RationalCostModel) (W T m K R : ℕ) : ℕ :=
  2*columnsProfile W T m K R+
    GeneralPaperNativePayloadFillStorage.profile W (columnProfile W T K R) m (fieldPrice model W K R) 0+
    fieldProfile model W K R+2*R+2*model.rat R+5*(natBits (metadataCap model W m K R)+W)+160*W

theorem field_work {T m K : ℕ} (model : RationalCostModel) (W R : ℕ) (c : ℚ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (hc : rationalWordWidth c≤R) (hx : ∀ j l,rationalWordWidth ((columns.read j).anchors.read l)≤R)
    (hp : ∀ j l,rationalWordWidth (c*(columns.read j).anchors.read l)≤R)
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (j : Fin m) : (field model W c columns j).2≤fieldPrice model W K R :=
  Nat.add_le_add_right (GeneralPaperRationalArrayScaleStorage.work model W R c (columns.read j).anchors hc (hx j) (hp j) hW hK) _

theorem field_bound {T K : ℕ} (model : RationalCostModel) (W R : ℕ) (c : ℚ) (old : GeneralPaperQuantizedColumn.Column T K)
    (hc : rationalWordWidth c≤R) (hx : ∀ l,rationalWordWidth (old.anchors.read l)≤R)
    (hp : ∀ l,rationalWordWidth (c*old.anchors.read l)≤R) (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W)
    (inner : ℕ) (hi : inner≤K) : fieldWindow model W c old inner hi≤fieldProfile model W K R := by
  have hArray := GeneralPaperRationalArrayScaleStorage.bounded model W R c old.anchors hc hx hp hW hK inner hi
  have hWork := GeneralPaperRationalArrayScaleStorage.work model W R c old.anchors hc hx hp hW hK
  have hf := fields_bound W (natBits (fieldCap model W K R))
    [(GeneralPaperRationalOutputScale.run model.rat (fun w => w) W c old.anchors).2,96*W,
      (GeneralPaperRationalOutputScale.run model.rat (fun w => w) W c old.anchors).2+96*W] (by
    intro z hz; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold fieldCap fieldPrice
    rcases hz with rfl|rfl|rfl <;> omega)
  change fields W _≤3*(natBits (fieldCap model W K R)+W)+32*W at hf
  unfold fieldWindow fieldProfile
  dsimp only
  omega

theorem work {T m K : ℕ} (model : RationalCostModel) (W R : ℕ) (budget : ℚ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (hb : rationalWordWidth budget≤R) (hc : rationalWordWidth budget⁻¹≤R)
    (hx : ∀ j l,rationalWordWidth ((columns.read j).anchors.read l)≤R)
    (hp : ∀ j l,rationalWordWidth (budget⁻¹*(columns.read j).anchors.read l)≤R)
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W) :
    (GeneralPaperNativeDictionaryNormalize.run model.rat (fun w => w) W budget columns).2≤price model W m K R := by
  have hScale := GeneralPaperNativePayloadFillStorage.prefix_work W (fieldPrice model W K R) (field model W budget⁻¹ columns)
    (field_work model W R budget⁻¹ columns hc hx hp hW hK) hW hM m le_rfl
  have hInv := GeneralPaperRationalPrimitivePrice.unary_le model.rat model.monotone (fun x => x⁻¹) budget R hb hc
  change (GeneralPaperNativeDictionaryNormalize.scale model.rat (fun w => w) W budget⁻¹ columns).2≤scalePrice model W m K R at hScale
  unfold GeneralPaperNativeDictionaryNormalize.run price
  dsimp only
  omega

theorem bounded {T m K : ℕ} (model : RationalCostModel) (W R : ℕ) (budget : ℚ)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column T K))
    (hb : rationalWordWidth budget≤R) (hc : rationalWordWidth budget⁻¹≤R)
    (hx : ∀ j l,rationalWordWidth ((columns.read j).anchors.read l)≤R)
    (hp : ∀ j l,rationalWordWidth (budget⁻¹*(columns.read j).anchors.read l)≤R)
    (hW : 1≤W) (hK : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (outer : ℕ) (ho : outer≤m) (inner : ℕ) (hi : inner≤K) (active : Option (Fin m)) :
    window model W budget columns outer ho inner hi active≤profile model W T m K R := by
  have hOld := columns_bound W R columns hx
  have hReturned := columns_bound W R (GeneralPaperNativeDictionaryNormalize.run model.rat (fun w => w) W budget columns).1 (by
    intro j l
    change rationalWordWidth (((GeneralPaperNativeDictionaryNormalize.scale model.rat (fun w => w) W budget⁻¹ columns).1.read j).anchors.read l)≤R
    rw [GeneralPaperNativeDictionaryNormalize.scale_data,FixedArrayTable.read_ofFn,FixedArrayTable.read_ofFn]
    exact hp j l)
  have hPayload (j : Fin m) : columnFoot W (field model W budget⁻¹ columns j).1≤columnProfile W T K R := by
    apply column_bound
    intro l
    change rationalWordWidth ((GeneralPaperRationalOutputScale.run model.rat (fun w => w) W budget⁻¹ (columns.read j).anchors).1.read l)≤R
    rw [GeneralPaperRationalOutputScale.data,FixedArrayTable.read_ofFn]
    exact hp j l
  have hFill := GeneralPaperNativePayloadFillStorage.bounded W (columnProfile W T K R) (fieldPrice model W K R) 0 (columnFoot W)
    (field model W budget⁻¹ columns) (fun _ => 0) hPayload (field_work model W R budget⁻¹ columns hc hx hp hW hK)
    (fun _ => Nat.le_refl _) hW hM outer ho
  have hActive : (match active with | none => 0 | some j => fieldWindow model W budget⁻¹ (columns.read j) inner hi)≤fieldProfile model W K R := by
    cases active with
    | none => exact Nat.zero_le _
    | some j => exact field_bound model W R budget⁻¹ (columns.read j) hc (hx j) (hp j) hW hK inner hi
  have hWork := work model W R budget columns hb hc hx hp hW hK hM
  have hInv := GeneralPaperRationalPrimitivePrice.unary_le model.rat model.monotone (fun x => x⁻¹) budget R hb hc
  have hShape : (GeneralPaperNativeDictionaryNormalize.run model.rat (fun w => w) W budget columns).2=
      (GeneralPaperNativeDictionaryNormalize.scale model.rat (fun w => w) W budget⁻¹ columns).2+
        GeneralPaperRationalPrimitivePrice.unary model.rat (fun x => x⁻¹) budget+32*W := rfl
  have hf := fields_bound W (natBits (metadataCap model W m K R)) (controls model W budget columns) (by
    intro z hz; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    unfold controls at hz
    dsimp only at hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold metadataCap
    rcases hz with rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤5*(natBits (metadataCap model W m K R)+W)+32*W at hf
  unfold window profile
  dsimp only
  omega

end Blotto.GeneralPaperDictionaryNormalizationStorage
