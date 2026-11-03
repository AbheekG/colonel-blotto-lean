import Blotto.GeneralPaperNativeIndexedScatterStorage

/-! Literal occurrence-label scatter through the stored original row
keys. Full order/returned-label arrays, default-buffer construction,
selected writes, recursive frames and one actual division callback coexist.
No inverse search, permutation replacement or row relabelling executes. -/
namespace Blotto.GeneralPaperQuantizedLabelScatterStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384

def callbackPrice (model : RationalCostModel) (W T B : ℕ) : ℕ := GeneralPaperNativeBlockLabelStorage.price model W T B+64*W
def entryCap (model : RationalCostModel) (W T B : ℕ) : ℕ := T+callbackPrice model W T B+1
def entryWindow {K B : ℕ} (model : RationalCostModel) (W : ℕ) (hB : 0<B)
    (order : FixedArrayTable (K*B) (Fin (K*B))) (r : Fin (K*B)) : ℕ :=
  let label := GeneralPaperNativeBlockLabel.run model.rat W hB r
  GeneralPaperNativeBlockLabelStorage.window model W hB r+
    fields W [r.val,(order.read r).val,label.2,label.2+64*W,64*W]+128*W
def entryProfile (model : RationalCostModel) (W T B : ℕ) : ℕ :=
  GeneralPaperNativeBlockLabelStorage.profile model W T B+5*(natBits (entryCap model W T B)+W)+160*W
def price (model : RationalCostModel) (W T B : ℕ) : ℕ :=
  GeneralPaperNativeIndexedScatterStorage.price W T T (callbackPrice model W T B)
def metadataCap (model : RationalCostModel) (W T K B : ℕ) : ℕ := T+K+B+price model W T B+64*W+1
def window {K B : ℕ} (model : RationalCostModel) (W : ℕ) (hK : 0<K) (hB : 0<B)
    (order : FixedArrayTable (K*B) (Fin (K*B))) (initialCount : ℕ) (hi : initialCount≤K*B)
    (count : ℕ) (hc : count≤K*B) (active : Option (Fin (K*B))) : ℕ :=
  arrayFootprint W (fun i : Fin (K*B) => natBits i.val) order+
    GeneralPaperNativeIndexedScatterStorage.window W (fun l : Fin K => natBits l.val) ⟨0,hK⟩
      (GeneralPaperNativeQuantizedLabels.entry model.rat W hB order) (entryWindow model W hB order)
      initialCount hi count hc active+
    fields W [K,B,K*B,(GeneralPaperNativeQuantizedLabels.run model.rat (fun w => w) W hK hB order).2,64*W]+128*W
def profile (model : RationalCostModel) (W T K B : ℕ) : ℕ :=
  arrayProfile W T (natBits T)+GeneralPaperNativeIndexedScatterStorage.profile W (natBits K) T T
    (callbackPrice model W T B) (entryProfile model W T B)+5*(natBits (metadataCap model W T K B)+W)+160*W

theorem entry_work {K B : ℕ} (model : RationalCostModel) (W : ℕ) (hB : 0<B)
    (order : FixedArrayTable (K*B) (Fin (K*B))) (r : Fin (K*B)) :
    (GeneralPaperNativeQuantizedLabels.entry model.rat W hB order r).2≤callbackPrice model W (K*B) B :=
  Nat.add_le_add_right (GeneralPaperNativeBlockLabelStorage.work model W (K*B) hB r r.isLt.le) _

theorem entry_bound {K B : ℕ} (model : RationalCostModel) (W : ℕ) (hB : 0<B)
    (order : FixedArrayTable (K*B) (Fin (K*B))) (r : Fin (K*B)) :
    entryWindow model W hB order r≤entryProfile model W (K*B) B := by
  have hDivision := GeneralPaperNativeBlockLabelStorage.bounded model W (K*B) hB r r.isLt.le
  have hWork := GeneralPaperNativeBlockLabelStorage.work model W (K*B) hB r r.isLt.le
  have hf := fields_bound W (natBits (entryCap model W (K*B) B))
    [r.val,(order.read r).val,(GeneralPaperNativeBlockLabel.run model.rat W hB r).2,
      (GeneralPaperNativeBlockLabel.run model.rat W hB r).2+64*W,64*W] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl
      all_goals unfold entryCap callbackPrice; omega)
  change fields W _≤5*(natBits (entryCap model W (K*B) B)+W)+32*W at hf
  unfold entryWindow entryProfile
  dsimp only
  omega

theorem work {K B : ℕ} (model : RationalCostModel) (W : ℕ) (hK : 0<K) (hB : 0<B)
    (order : FixedArrayTable (K*B) (Fin (K*B))) (hW : 1≤W) (hIndex : binaryWordWidth (K*B+K*B+1)≤W) :
    (GeneralPaperNativeQuantizedLabels.run model.rat (fun w => w) W hK hB order).2≤price model W (K*B) B :=
  GeneralPaperNativeIndexedScatterStorage.work W (callbackPrice model W (K*B) B) (⟨0,hK⟩ : Fin K)
    (GeneralPaperNativeQuantizedLabels.entry model.rat W hB order) (entry_work model W hB order) hW hIndex

theorem bounded {K B : ℕ} (model : RationalCostModel) (W : ℕ) (hK : 0<K) (hB : 0<B)
    (order : FixedArrayTable (K*B) (Fin (K*B))) (hW : 1≤W) (hIndex : binaryWordWidth (K*B+K*B+1)≤W)
    (initialCount : ℕ) (hi : initialCount≤K*B) (count : ℕ) (hc : count≤K*B) (active : Option (Fin (K*B))) :
    window model W hK hB order initialCount hi count hc active≤profile model W (K*B) K B := by
  let encode := fun l : Fin K => natBits l.val
  have hOrder := array_bound W (natBits (K*B)) (fun i : Fin (K*B) => natBits i.val) order
    (fun i => Nat.add_le_add_left (binaryWordWidth_mono (order.read i).isLt.le) 1)
  have hScatter := GeneralPaperNativeIndexedScatterStorage.bounded W (natBits K) (callbackPrice model W (K*B) B)
    (entryProfile model W (K*B) B) encode ⟨0,hK⟩ (GeneralPaperNativeQuantizedLabels.entry model.rat W hB order)
    (entryWindow model W hB order) (Nat.add_le_add_left (binaryWordWidth_mono (Nat.zero_le K)) 1)
    (fun i => Nat.add_le_add_left (binaryWordWidth_mono (GeneralPaperNativeQuantizedLabels.entry model.rat W hB order i).1.2.isLt.le) 1)
    (entry_work model W hB order) (entry_bound model W hB order) hW hIndex initialCount hi count hc active
  dsimp only [encode] at hScatter
  have hWork := work model W hK hB order hW hIndex
  have hf := fields_bound W (natBits (metadataCap model W (K*B) K B))
    [K,B,K*B,(GeneralPaperNativeQuantizedLabels.run model.rat (fun w => w) W hK hB order).2,64*W] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change fields W _≤5*(natBits (metadataCap model W (K*B) K B)+W)+32*W at hf
  unfold window profile
  omega

theorem price_mono (model : RationalCostModel) (W T b B : ℕ) (hb : b≤B) : price model W T b≤price model W T B := by
  have h := GeneralPaperNativeBlockLabelStorage.price_mono model W T T b B le_rfl hb
  unfold price callbackPrice GeneralPaperNativeIndexedScatterStorage.price
  gcongr

theorem profile_mono (model : RationalCostModel) (W T K b B : ℕ) (hb : b≤B) :
    profile model W T K b≤profile model W T K B := by
  have hPrice := price_mono model W T b B hb
  have hD := GeneralPaperNativeBlockLabelStorage.price_mono model W T T b B le_rfl hb
  have hDP := GeneralPaperNativeBlockLabelStorage.profile_mono model W T T b B le_rfl hb
  have hC : callbackPrice model W T b≤callbackPrice model W T B := Nat.add_le_add_right hD _
  have hE : entryProfile model W T b≤entryProfile model W T B := by
    unfold entryProfile entryCap natBits
    gcongr
  have hS := GeneralPaperNativeIndexedScatterStorage.profile_mono W (natBits K) T T _ _ _ _ hC hE
  unfold natBits at hS
  unfold profile metadataCap natBits
  gcongr

end Blotto.GeneralPaperQuantizedLabelScatterStorage
