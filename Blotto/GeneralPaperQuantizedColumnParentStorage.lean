import Blotto.GeneralPaperSourceLabelScatterReachedRates

/-! Native quantized-column caller. Input values, stored stable order,
completed label/anchor arrays and returned column coexist with the literal
native child/partial/return counters. Child scratch remains in the checked
sort/scatter/anchor windows; whole child work sizes only encoded metadata. -/
namespace Blotto.GeneralPaperQuantizedColumnParentStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage GeneralPaperEnclosingSourceOwners
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384

def price (model : RationalCostModel) (W T K B R : ℕ) : ℕ :=
  GeneralPaperRepresentativeSortStorage.price model W T R+GeneralPaperQuantizedLabelScatterStorage.price model W T B+
    GeneralPaperQuantizedAnchorStorage.price model W T K+64*W
def metadataCap (model : RationalCostModel) (W T K B R : ℕ) : ℕ := T+K+B+price model W T K B R+64*W+1
def window {K B : ℕ} (model : RationalCostModel) (W : ℕ) (hK : 0<K) (hB : 0<B) (value : FixedArrayTable (K*B) ℚ) : ℕ :=
  let sorted := GeneralPaperNativeRepresentativeSort.run model.rat (fun w => w) W value
  let labels := GeneralPaperNativeQuantizedLabels.run model.rat (fun w => w) W hK hB sorted.1
  let anchors := GeneralPaperNativeQuantizedAnchors.run model.rat (fun w => w) W hB sorted.1 value
  let result := GeneralPaperNativeQuantizedColumn.run model.rat (fun w => w) W hK hB value
  arrayFootprint W rationalWordWidth value+arrayFootprint W (fun i : Fin (K*B) => natBits i.val) sorted.1+
    2*columnFoot W result.1+fields W [K,B,K*B,sorted.2,labels.2,anchors.2,result.2,
      sorted.2+labels.2,sorted.2+labels.2+anchors.2,64*W]+128*W
def profile (model : RationalCostModel) (W T K B R : ℕ) : ℕ :=
  arrayProfile W T R+arrayProfile W T (natBits T)+2*columnProfile W T K R+
    10*(natBits (metadataCap model W T K B R)+W)+160*W

theorem anchors_word {K B : ℕ} (model : RationalCostModel) (W R : ℕ) (hK : 0<K) (hB : 0<B)
    (value : FixedArrayTable (K*B) ℚ) (hR : 3≤R) (hv : ∀ i,rationalWordWidth (value.read i)≤R) (l : Fin K) :
    rationalWordWidth ((GeneralPaperNativeQuantizedColumn.run model.rat (fun w => w) W hK hB value).1.anchors.read l)≤R := by
  change rationalWordWidth ((GeneralPaperNativeQuantizedAnchors.run model.rat (fun w => w) W hB
    (GeneralPaperNativeRepresentativeSort.run model.rat (fun w => w) W value).1 value).1.read l)≤R
  unfold GeneralPaperNativeQuantizedAnchors.run
  rw [PaperIndexedArrayConstruction.run_data,FixedArrayTable.read_ofFn]
  exact GeneralPaperQuantizedAnchorStorage.entry_word model W R hB _ value hR hv l

theorem work {K B : ℕ} (model : RationalCostModel) (W R : ℕ) (hK : 0<K) (hB : 0<B)
    (value : FixedArrayTable (K*B) ℚ) (hv : ∀ i,rationalWordWidth (value.read i)≤R)
    (hW : 1≤W) (hIndex : binaryWordWidth (K*B+K*B+1)≤W) (hLabels : binaryWordWidth (K+1)≤W) :
    (GeneralPaperNativeQuantizedColumn.run model.rat (fun w => w) W hK hB value).2≤price model W (K*B) K B R := by
  have hT : binaryWordWidth (K*B+1)≤W := (binaryWordWidth_mono (by omega)).trans hIndex
  have hSort := GeneralPaperRepresentativeSortStorage.work model W R value hv hW hT
  have hScatter := GeneralPaperQuantizedLabelScatterStorage.work model W hK hB
    (GeneralPaperNativeRepresentativeSort.run model.rat (fun w => w) W value).1 hW hIndex
  have hAnchors := GeneralPaperQuantizedAnchorStorage.work model W hK hB
    (GeneralPaperNativeRepresentativeSort.run model.rat (fun w => w) W value).1 value hW hLabels
  unfold GeneralPaperNativeQuantizedColumn.run price
  dsimp only
  omega

theorem bounded {K B : ℕ} (model : RationalCostModel) (W R : ℕ) (hK : 0<K) (hB : 0<B)
    (value : FixedArrayTable (K*B) ℚ) (hR : 3≤R) (hv : ∀ i,rationalWordWidth (value.read i)≤R)
    (hW : 1≤W) (hIndex : binaryWordWidth (K*B+K*B+1)≤W) (hLabels : binaryWordWidth (K+1)≤W) :
    window model W hK hB value≤profile model W (K*B) K B R := by
  let sorted := GeneralPaperNativeRepresentativeSort.run model.rat (fun w => w) W value
  let labels := GeneralPaperNativeQuantizedLabels.run model.rat (fun w => w) W hK hB sorted.1
  let anchors := GeneralPaperNativeQuantizedAnchors.run model.rat (fun w => w) W hB sorted.1 value
  let result := GeneralPaperNativeQuantizedColumn.run model.rat (fun w => w) W hK hB value
  have hValue := array_bound W R rationalWordWidth value hv
  have hOrder := array_bound W (natBits (K*B)) (fun i : Fin (K*B) => natBits i.val) sorted.1
    (fun i => Nat.add_le_add_left (binaryWordWidth_mono (sorted.1.read i).isLt.le) 1)
  have hColumn := column_bound W R result.1 (anchors_word model W R hK hB value hR hv)
  have hWork := work model W R hK hB value hv hW hIndex hLabels
  change result.2≤price model W (K*B) K B R at hWork
  have hShape : result.2=sorted.2+labels.2+anchors.2+64*W := rfl
  have hf := fields_bound W (natBits (metadataCap model W (K*B) K B R))
    [K,B,K*B,sorted.2,labels.2,anchors.2,result.2,sorted.2+labels.2,sorted.2+labels.2+anchors.2,64*W] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change fields W _≤10*(natBits (metadataCap model W (K*B) K B R)+W)+32*W at hf
  change arrayFootprint W rationalWordWidth value+arrayFootprint W (fun i : Fin (K*B) => natBits i.val) sorted.1+
    2*columnFoot W result.1+fields W [K,B,K*B,sorted.2,labels.2,anchors.2,result.2,
      sorted.2+labels.2,sorted.2+labels.2+anchors.2,64*W]+128*W≤_
  unfold profile
  omega

theorem price_mono (model : RationalCostModel) (W T K b B R : ℕ) (hb : b≤B) :
    price model W T K b R≤price model W T K B R := by
  have h := GeneralPaperQuantizedLabelScatterStorage.price_mono model W T b B hb
  unfold price
  omega

theorem profile_mono (model : RationalCostModel) (W T K b B R : ℕ) (hb : b≤B) :
    profile model W T K b R≤profile model W T K B R := by
  have h := price_mono model W T K b B R hb
  unfold profile metadataCap natBits
  gcongr

end Blotto.GeneralPaperQuantizedColumnParentStorage
