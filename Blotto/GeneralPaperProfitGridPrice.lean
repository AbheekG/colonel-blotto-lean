import Blotto.GeneralPaperProfitOrderConstruction

/-! The complete fixed profit-grid record, including its two arrays,
denominator, search depth and exact native work annotations. Each child is
called once; proofs used in the record are erased construction certificates.
-/
namespace Blotto.GeneralPaperProfitGridPrice
open GeneralPaperProfitGridPoints
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def tableRun (index : ℕ → ℕ) (W : ℕ) (values : List ℕ) : FixedArrayTable values.length ℕ × ℕ :=
  let array := PaperListReferenceArray.run index W values
  (⟨array.1,PaperListReferenceArray.size index W values⟩,array.2)

theorem table_data (index : ℕ → ℕ) (W : ℕ) (values : List ℕ) :
    (tableRun index W values).1=⟨values.toArray,by simp⟩ := by
  unfold tableRun
  simp only [PaperListReferenceArray.data]

def rawWork (primitive : ℕ → ℕ) (size : ℕ) : ℕ :=
  GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a*b) 58 size+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) (58*size) 18+
    GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) size 1

def assemble (index primitive : ℕ → ℕ) (W q w B : ℕ) (values : List ℕ) (den : ℕ)
    (hValues : values=GeneralPaperProfitGridPrepare.ordered w B) : GeneralPaperProfitGridPrepare.Prepared q w B × ℕ :=
  let table := tableRun index W values
  let leaf := GeneralPaperProfitScalePrice.run index primitive W q table.1
  let cap := GeneralPaperPowerCeilingBits.run primitive W (values.length+1)
  let prepared : GeneralPaperProfitGridPrepare.Prepared q w B :=
    ⟨values.length,table.1,leaf.1,cap.1.doublings,den,58*values.length+18,cap.1.work,
      by rw [hValues]; exact GeneralPaperSortedBreakpoints.ordered_positive _ _,by
        have hLower := GeneralPaperPowerCeiling.ceiling_lower (values.length+1)
        rw [GeneralPaperPowerCeiling.ceiling_power] at hLower
        change values.length<2^cap.1.doublings
        rw [GeneralPaperPowerCeilingBits.data]
        omega⟩
  (prepared,table.2+leaf.2+cap.2+rawWork primitive values.length+128*(values.length+1)*W)

theorem assemble_data (index primitive : ℕ → ℕ) (W q w B : ℕ) (values : List ℕ) (den : ℕ)
    (hValues : values=GeneralPaperProfitGridPrepare.ordered w B) (hDen : den=denominator w B) :
    (assemble index primitive W q w B values den hValues).1=GeneralPaperProfitGridPrepare.prepare q w B := by
  subst values; subst den
  have h := GeneralPaperProfitGridPrepare.scaled_work q w B
  change (GeneralPaperProfitGridPrepare.scaled q
    (⟨(GeneralPaperProfitGridPrepare.ordered w B).toArray,by simp⟩ :
      FixedArrayTable (GeneralPaperProfitGridPrepare.ordered w B).length ℕ)).2=
        58*(GeneralPaperProfitGridPrepare.ordered w B).length+18 at h
  simp only [assemble,table_data,GeneralPaperProfitScalePrice.data,
    GeneralPaperPowerCeilingBits.data,GeneralPaperProfitGridPrepare.prepare,h]

def run (index primitive : ℕ → ℕ) (W q w B : ℕ) : GeneralPaperProfitGridPrepare.Prepared q w B × ℕ :=
  let ordered := GeneralPaperProfitOrderConstruction.run primitive W w B
  let grid := assemble index primitive W q w B ordered.1.1 ordered.1.2
    (congrArg Prod.fst (GeneralPaperProfitOrderConstruction.data primitive W w B))
  (grid.1,ordered.2+grid.2)

theorem data (index primitive : ℕ → ℕ) (W q w B : ℕ) :
    (run index primitive W q w B).1=GeneralPaperProfitGridPrepare.prepare q w B :=
  assemble_data index primitive W q w B _ _
    (congrArg Prod.fst (GeneralPaperProfitOrderConstruction.data primitive W w B))
    (congrArg Prod.snd (GeneralPaperProfitOrderConstruction.data primitive W w B))

theorem raw_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (w B size : ℕ)
    (hSize : size≤(B+1)*w+2) :
    rawWork primitive size≤6*primitive (2*GeneralPaperProfitOrderPrice.word w B) := by
  let W := GeneralPaperProfitOrderPrice.word w B
  have hW : 128≤W := by unfold W GeneralPaperProfitOrderPrice.word; omega
  have hCap : size≤GeneralPaperProfitOrderPrice.capacity w B := by
    unfold GeneralPaperProfitOrderPrice.capacity
    nlinarith only [hSize,Nat.zero_le B]
  have hn := GeneralPaperProfitOrderPrice.bounded w B size (by omega)
  have hm := GeneralPaperProfitOrderPrice.bounded w B (58*size) (by omega)
  have hs := GeneralPaperProfitOrderPrice.bounded w B (58*size+18) (by omega)
  have hp := GeneralPaperProfitOrderPrice.bounded w B (size+1) (by omega)
  have h58 : binaryWordWidth 58=6 := by decide
  have h18 : binaryWordWidth 18=5 := by decide
  have h1 : binaryWordWidth 1=1 := by decide
  have hMul := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a*b) 58 size (2*W)
    (by omega) (by change binaryWordWidth size≤W at hn; omega)
    (by change binaryWordWidth (58*size)≤W at hm; omega)
  have hAdd := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) (58*size) 18 (2*W)
    (by change binaryWordWidth (58*size)≤W at hm; omega) (by omega)
    (by change binaryWordWidth (58*size+18)≤W at hs; omega)
  have hTarget := GeneralPaperIntegerWordPrice.natural_binary primitive hMono (fun a b => a+b) size 1 (2*W)
    (by change binaryWordWidth size≤W at hn; omega) (by omega)
    (by change binaryWordWidth (size+1)≤W at hp; omega)
  unfold rawWork
  change _≤6*primitive (2*W)
  omega

def count (w B : ℕ) : ℕ := (B+1)*w+2

def depthProfile (primitive : ℕ → ℕ) (W w B : ℕ) : ℕ :=
  64*(binaryWordWidth (count w B+1)+1)*(W+primitive (1+binaryWordWidth (2*(count w B+2))))

def profile (primitive : ℕ → ℕ) (W q w B : ℕ) : ℕ :=
  GeneralPaperProfitOrderConstruction.profile primitive W w B+
    252*(count w B+1)*W+count w B*(2*primitive (GeneralPaperProfitScalePrice.width q w B))+
    depthProfile primitive W w B+6*primitive (2*GeneralPaperProfitOrderPrice.word w B)

theorem work (index primitive : ℕ → ℕ) (hMono : Monotone primitive) (W q w B : ℕ)
    (hW : 1≤W) (hIndex : ∀ i≤count w B,index (binaryWordWidth (i+1))≤W) :
    (run index primitive W q w B).2≤profile primitive W q w B := by
  let ordered := GeneralPaperProfitOrderConstruction.run primitive W w B
  let values := ordered.1.1
  let table := tableRun index W values
  have hValues : values=GeneralPaperProfitGridPrepare.ordered w B :=
    congrArg Prod.fst (GeneralPaperProfitOrderConstruction.data primitive W w B)
  have hN : values.length≤count w B := by
    rw [hValues]
    exact GeneralPaperProfitGridPrepare.size_bound q w B
  have hI : ∀ i≤values.length,index (binaryWordWidth (i+1))≤W := fun i hi => hIndex i (hi.trans hN)
  have hOrder := GeneralPaperProfitOrderConstruction.work primitive hMono W w B
  have hArray := GeneralPaperControlArrayPrice.list_work index W values hW hI
  change table.2≤64*(values.length+1)*W at hArray
  have hNumerators : ∀ i,table.1.read i≤2*denominator w B := by
    intro i
    have hMember : values[i.val]∈GeneralPaperProfitGridPrepare.ordered w B := by
      rw [←hValues]
      exact List.getElem_mem _
    have hb := GeneralPaperSortedBreakpoints.ordered_bound (2*denominator w B) (points w B) values[i.val] hMember
    simpa only [table,table_data,FixedArrayTable.read,List.getElem_toArray] using hb
  have hLeaf := GeneralPaperProfitScalePrice.work index primitive hMono W q w B table.1 hNumerators hW hI
  have hDepth := GeneralPaperPowerCeilingBits.work primitive hMono W (values.length+1)
  have hRaw := raw_work primitive hMono w B values.length hN
  have hDepthWidth := hMono (Nat.add_le_add_left
    (binaryWordWidth_mono (show 2*(values.length+1+1)≤2*(count w B+2) by omega)) 1)
  have hDepthCount := binaryWordWidth_mono (Nat.add_le_add_right hN 1)
  have hDepthBound := Nat.mul_le_mul
    (Nat.mul_le_mul_left 64 (Nat.add_le_add_right hDepthCount 1))
    (Nat.add_le_add_left hDepthWidth W)
  have hD : (GeneralPaperPowerCeilingBits.run primitive W (values.length+1)).2≤depthProfile primitive W w B :=
    hDepth.trans hDepthBound
  have hArrayBound := Nat.mul_le_mul_right W (Nat.mul_le_mul_left 64 (Nat.add_le_add_right hN 1))
  have hLeafBound := Nat.add_le_add
    (Nat.mul_le_mul_right (2*primitive (GeneralPaperProfitScalePrice.width q w B)+16*W) hN)
    (Nat.mul_le_mul_right W (Nat.mul_le_mul_left 44 (Nat.add_le_add_right hN 1)))
  have hRecordBound := Nat.mul_le_mul_right W (Nat.mul_le_mul_left 128 (Nat.add_le_add_right hN 1))
  change ordered.2+(table.2+(GeneralPaperProfitScalePrice.run index primitive W q table.1).2+
    (GeneralPaperPowerCeilingBits.run primitive W (values.length+1)).2+rawWork primitive values.length+
      128*(values.length+1)*W)≤_
  change ordered.2≤_ at hOrder
  unfold profile
  nlinarith only [hOrder,hArray,hLeaf,hD,hRaw,hArrayBound,hLeafBound,hRecordBound]

theorem bit_work (model : RationalCostModel) (q w B : ℕ) :
    (run (fun a => a) model.rat (GeneralPaperProfitOrderPrice.word w B) q w B).2≤
      profile model.rat (GeneralPaperProfitOrderPrice.word w B) q w B := by
  apply work _ _ model.monotone
  · unfold GeneralPaperProfitOrderPrice.word; omega
  · intro i hi
    exact GeneralPaperProfitOrderPrice.reference_indices w B i (by
      rw [points_length]
      exact hi)

theorem arithmetic_work (q w B : ℕ) :
    (run (fun _ => 1) (fun _ => 1) 1 q w B).2≤profile (fun _ => 1) 1 q w B :=
  work _ _ (fun _ _ _ => Nat.le_refl 1) _ _ _ _ (Nat.le_refl 1) (fun _ _ => Nat.le_refl 1)

theorem same_data (index primitive : ℕ → ℕ) (W q w B : ℕ) :
    (run index primitive W q w B).1=(run (fun _ => 1) (fun _ => 1) 1 q w B).1 := by rw [data,data]

end Blotto.GeneralPaperProfitGridPrice
