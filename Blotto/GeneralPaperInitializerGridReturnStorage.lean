import Blotto.GeneralPaperSourceBasisGridPackingStorageReachedRates

/-! Literal grid-construction parent return. Full retained quotient/value
table, packed and returned grid vectors, original N/depth and six native
caller fields coexist with dictionary/view references. The original
prepared dictionary/labels remain shared caller owners, not copied here. -/
namespace Blotto.GeneralPaperInitializerGridReturnStorage
open RationalOrderCell GeneralPaperEncodedScalarStorage
open GeneralPaperEncodedBasisStorage (integerBits arrayFootprint)
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192

def tableFoot {m K : ℕ} (W : ℕ) (table : GeneralPaperInitializerStoredBits.Table m K) : ℕ :=
  arrayFootprint W (arrayFootprint W (GeneralPaperInitializerTableStorage.pairFoot W)) table
def metadataCap (W R A B : ℕ) : ℕ := R+A+B+32*W+1
def controls {T m K : ℕ} (model : RationalCostModel) (W N depth : ℕ) (dict : GeneralPaperDictionary.Dictionary T m K) : List ℕ :=
  let stored := GeneralPaperInitializerStoredBits.run model W N depth dict.anchor
  let packed := GeneralPaperBasisGridPackingPrice.run (fun w => w) model.rat W (GeneralPaperInitializerGridPrice.values stored.1)
  let result := GeneralPaperInitializerGridPrice.run model W N depth dict
  [depth,stored.2,packed.2,result.2,16*W,stored.2+packed.2]
def window {T m K : ℕ} (model : RationalCostModel) (W N depth : ℕ) (dict : GeneralPaperDictionary.Dictionary T m K) : ℕ :=
  let stored := GeneralPaperInitializerStoredBits.run model W N depth dict.anchor
  let packed := GeneralPaperBasisGridPackingPrice.run (fun w => w) model.rat W (GeneralPaperInitializerGridPrice.values stored.1)
  let result := GeneralPaperInitializerGridPrice.run model W N depth dict
  tableFoot W stored.1+arrayFootprint W integerBits packed.1+arrayFootprint W integerBits result.1.2+natBits N+
    fields W (controls model W N depth dict)+96*W
def profile (W Btable Bgrid P R A B : ℕ) : ℕ := Btable+2*Bgrid+P+6*(natBits (metadataCap W R A B)+W)+128*W

theorem work {T m K : ℕ} (model : RationalCostModel) (W N depth A B : ℕ) (dict : GeneralPaperDictionary.Dictionary T m K)
    (hStored : (GeneralPaperInitializerStoredBits.run model W N depth dict.anchor).2≤A)
    (hPacked : (GeneralPaperBasisGridPackingPrice.run (fun w => w) model.rat W
      (GeneralPaperInitializerGridPrice.values (GeneralPaperInitializerStoredBits.run model W N depth dict.anchor).1)).2≤B) :
    (GeneralPaperInitializerGridPrice.run model W N depth dict).2≤A+B+16*W := by
  change (GeneralPaperInitializerStoredBits.run model W N depth dict.anchor).2+_+16*W≤_
  omega

theorem bounded {T m K : ℕ} (model : RationalCostModel) (W N depth Btable Bgrid P R A B : ℕ)
    (dict : GeneralPaperDictionary.Dictionary T m K)
    (hTable : tableFoot W (GeneralPaperInitializerStoredBits.run model W N depth dict.anchor).1≤Btable)
    (hGrid : arrayFootprint W integerBits (GeneralPaperBasisGridPackingPrice.run (fun w => w) model.rat W
      (GeneralPaperInitializerGridPrice.values (GeneralPaperInitializerStoredBits.run model W N depth dict.anchor).1)).1≤Bgrid)
    (hN : natBits N≤P) (hd : depth≤R)
    (hStored : (GeneralPaperInitializerStoredBits.run model W N depth dict.anchor).2≤A)
    (hPacked : (GeneralPaperBasisGridPackingPrice.run (fun w => w) model.rat W
      (GeneralPaperInitializerGridPrice.values (GeneralPaperInitializerStoredBits.run model W N depth dict.anchor).1)).2≤B) :
    window model W N depth dict≤profile W Btable Bgrid P R A B := by
  let stored := GeneralPaperInitializerStoredBits.run model W N depth dict.anchor
  let packed := GeneralPaperBasisGridPackingPrice.run (fun w => w) model.rat W (GeneralPaperInitializerGridPrice.values stored.1)
  let result := GeneralPaperInitializerGridPrice.run model W N depth dict
  have hWork := work model W N depth A B dict hStored hPacked
  change result.2≤A+B+16*W at hWork
  change stored.2≤A at hStored
  change packed.2≤B at hPacked
  have hReturned : arrayFootprint W integerBits result.1.2≤Bgrid := hGrid
  have hf := fields_bound W (natBits (metadataCap W R A B)) (controls model W N depth dict) (by
    intro z hz; apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    change z∈[depth,stored.2,packed.2,result.2,16*W,stored.2+packed.2] at hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold metadataCap
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W (controls model W N depth dict)≤6*(natBits (metadataCap W R A B)+W)+32*W at hf
  unfold window profile
  dsimp only
  dsimp only [result] at hReturned
  omega

end Blotto.GeneralPaperInitializerGridReturnStorage
