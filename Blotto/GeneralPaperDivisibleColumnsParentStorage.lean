import Blotto.GeneralPaperQuantizedMatrixParentStorage

/-! Actual divisible-column quantization caller. The native computed
block size, identical physical row/column casts, complete matrix caller
and one-time adaptive division coexist with original/returned owners and
all native parent counters. Child work only sizes encoded metadata. -/
namespace Blotto.GeneralPaperDivisibleColumnsParentStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEnclosingSourceOwners
set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option maxRecDepth 16384

def blockSize (model : RationalCostModel) (W T K : ℕ) (hK : 0<K) : ℕ :=
  (GeneralPaperNativeDivisibleColumns.blocks model.rat W T K hK).1.val

theorem size_eq (model : RationalCostModel) (W T K : ℕ) (hK : 0<K) (hDiv : K∣T) :
    T=K*blockSize model W T K hK := by
  unfold blockSize
  rw [GeneralPaperNativeDivisibleColumns.blocks_data]
  exact GeneralPaperRowQuantizer.divisor_size hDiv

theorem block_positive (model : RationalCostModel) (W T K : ℕ) (hT : 0<T) (hK : 0<K) (hDiv : K∣T) :
    0<blockSize model W T K hK := by
  unfold blockSize
  rw [GeneralPaperNativeDivisibleColumns.blocks_data]
  exact GeneralPaperRowQuantizer.divisor_block_pos hT hK hDiv

theorem block_bounded (model : RationalCostModel) (W T K : ℕ) (hK : 0<K) : blockSize model W T K hK≤T := by
  have h := (GeneralPaperNativeDivisibleColumns.blocks model.rat W T K hK).1.isLt
  exact Nat.le_of_lt_succ h

theorem cast_columns_foot {T U m K : ℕ} (W : ℕ) (h : T=U)
    (columns : FixedArrayTable m (GeneralPaperQuantizedColumn.Column U K)) :
    columnsFoot W (GeneralPaperNativeDivisibleColumns.castColumns h columns)=columnsFoot W columns := by
  subst U
  rfl

def price (model : RationalCostModel) (W T m K B R : ℕ) : ℕ :=
  GeneralPaperNativeBlockLabelStorage.price model W T K+GeneralPaperQuantizedMatrixParentStorage.price model W T m K B R+64*W
def metadataCap (model : RationalCostModel) (W T m K B R : ℕ) : ℕ := T+K+B+price model W T m K B R+64*W+1
def window {T m K : ℕ} (model : RationalCostModel) (W : ℕ) (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (outer : ℕ) (ho : outer≤m) (active : Option (Fin m)) : ℕ :=
  let B := blockSize model W T K hK
  let hs := size_eq model W T K hK hDiv
  let hp := block_positive model W T K hT hK hDiv
  let matrix := GeneralPaperNativeQuantizedMatrix.run model.rat (fun w => w) W hK hp (GeneralPaperRowQuantizer.castRows hs rows)
  let divided := GeneralPaperNativeDivisibleColumns.blocks model.rat W T K hK
  let result := GeneralPaperNativeDivisibleColumns.run model.rat (fun w => w) W hT hK hDiv rows
  rowsFoot W rows+columnsFoot W result.1+
    GeneralPaperQuantizedMatrixParentStorage.window model W hK hp (GeneralPaperRowQuantizer.castRows hs rows) outer ho active+
    GeneralPaperNativeBlockLabelStorage.window (K:=T+1) model W hK ⟨T,by nlinarith only [hK]⟩+
    fields W [T,K,B,divided.2,matrix.2,result.2,divided.2+matrix.2,64*W]+128*W
def profile (model : RationalCostModel) (W T m K B R : ℕ) : ℕ :=
  rowsProfile W T m R+columnsProfile W T m K R+GeneralPaperQuantizedMatrixParentStorage.profile model W T m K B R+
    GeneralPaperNativeBlockLabelStorage.profile model W T K+8*(natBits (metadataCap model W T m K B R)+W)+160*W

theorem work {T m K : ℕ} (model : RationalCostModel) (W R B : ℕ) (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (hv : ∀ i j,rationalWordWidth ((rows.read i).read j)≤R)
    (hB : blockSize model W T K hK≤B) (hW : 1≤W) (hIndex : binaryWordWidth (T+T+1)≤W)
    (hLabels : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W) :
    (GeneralPaperNativeDivisibleColumns.run model.rat (fun w => w) W hT hK hDiv rows).2≤price model W T m K B R := by
  let hs := size_eq model W T K hK hDiv
  let hp := block_positive model W T K hT hK hDiv
  have hCast := GeneralPaperNativeDivisibleColumns.cast_words hs rows R hv
  have hI : binaryWordWidth (K*blockSize model W T K hK+K*blockSize model W T K hK+1)≤W := by rw [←hs];exact hIndex
  have hDiv := GeneralPaperNativeBlockLabelStorage.work (K:=T+1) model W T hK ⟨T,by nlinarith only [hK]⟩ le_rfl
  have hMatrix := GeneralPaperQuantizedMatrixParentStorage.work model W R hK hp (GeneralPaperRowQuantizer.castRows hs rows)
    hCast hW hI hLabels hM
  have hMatrix' : (GeneralPaperNativeQuantizedMatrix.run model.rat (fun w => w) W hK hp (GeneralPaperRowQuantizer.castRows hs rows)).2≤
      GeneralPaperQuantizedMatrixParentStorage.price model W T m K B R := by
    apply hMatrix.trans
    rw [←hs]
    exact GeneralPaperQuantizedMatrixParentStorage.price_mono model W T m K _ _ R hB
  change (GeneralPaperNativeDivisibleColumns.blocks model.rat W T K hK).2+
    (GeneralPaperNativeQuantizedMatrix.run model.rat (fun w => w) W hK hp (GeneralPaperRowQuantizer.castRows hs rows)).2+64*W≤_
  change (GeneralPaperNativeDivisibleColumns.blocks model.rat W T K hK).2≤_ at hDiv
  unfold price
  omega

theorem bounded {T m K : ℕ} (model : RationalCostModel) (W R B : ℕ) (hT : 0<T) (hK : 0<K) (hDiv : K∣T)
    (rows : FixedArrayTable T (FixedArrayTable m ℚ)) (hR : 3≤R) (hv : ∀ i j,rationalWordWidth ((rows.read i).read j)≤R)
    (hB : blockSize model W T K hK≤B) (hW : 1≤W) (hIndex : binaryWordWidth (T+T+1)≤W)
    (hLabels : binaryWordWidth (K+1)≤W) (hM : binaryWordWidth (m+1)≤W)
    (outer : ℕ) (ho : outer≤m) (active : Option (Fin m)) :
    window model W hT hK hDiv rows outer ho active≤profile model W T m K B R := by
  let hs := size_eq model W T K hK hDiv
  let hp := block_positive model W T K hT hK hDiv
  let matrix := GeneralPaperNativeQuantizedMatrix.run model.rat (fun w => w) W hK hp (GeneralPaperRowQuantizer.castRows hs rows)
  let divided := GeneralPaperNativeDivisibleColumns.blocks model.rat W T K hK
  let result := GeneralPaperNativeDivisibleColumns.run model.rat (fun w => w) W hT hK hDiv rows
  have hCast := GeneralPaperNativeDivisibleColumns.cast_words hs rows R hv
  have hI : binaryWordWidth (K*blockSize model W T K hK+K*blockSize model W T K hK+1)≤W := by rw [←hs];exact hIndex
  have hRows := rows_bound W R rows hv
  have hReturn := GeneralPaperQuantizedMatrixParentStorage.returned_bound model W R hK hp (GeneralPaperRowQuantizer.castRows hs rows) hR hCast
  have hColumns : columnsFoot W result.1≤columnsProfile W T m K R := by
    change columnsFoot W (GeneralPaperNativeDivisibleColumns.castColumns hs matrix.1)≤_
    rw [cast_columns_foot]
    apply hReturn.trans
    rw [←hs]
  have hMatrix := GeneralPaperQuantizedMatrixParentStorage.bounded model W R hK hp (GeneralPaperRowQuantizer.castRows hs rows)
    hR hCast hW hI hLabels hM outer ho active
  have hMatrix' : GeneralPaperQuantizedMatrixParentStorage.window model W hK hp (GeneralPaperRowQuantizer.castRows hs rows) outer ho active≤
      GeneralPaperQuantizedMatrixParentStorage.profile model W T m K B R := by
    apply hMatrix.trans
    rw [←hs]
    exact GeneralPaperQuantizedMatrixParentStorage.profile_mono model W T m K _ _ R hB
  have hDivision := GeneralPaperNativeBlockLabelStorage.bounded (K:=T+1) model W T hK ⟨T,by nlinarith only [hK]⟩ le_rfl
  have hWork := work model W R B hT hK hDiv rows hv hB hW hIndex hLabels hM
  change result.2≤price model W T m K B R at hWork
  have hShape : result.2=divided.2+matrix.2+64*W := rfl
  have hf := fields_bound W (natBits (metadataCap model W T m K B R))
    [T,K,blockSize model W T K hK,divided.2,matrix.2,result.2,divided.2+matrix.2,64*W] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change fields W _≤8*(natBits (metadataCap model W T m K B R)+W)+32*W at hf
  change rowsFoot W rows+columnsFoot W result.1+
    GeneralPaperQuantizedMatrixParentStorage.window model W hK hp (GeneralPaperRowQuantizer.castRows hs rows) outer ho active+
    GeneralPaperNativeBlockLabelStorage.window (K:=T+1) model W hK ⟨T,by nlinarith only [hK]⟩+
    fields W [T,K,blockSize model W T K hK,divided.2,matrix.2,result.2,divided.2+matrix.2,64*W]+128*W≤_
  unfold profile
  omega

end Blotto.GeneralPaperDivisibleColumnsParentStorage
