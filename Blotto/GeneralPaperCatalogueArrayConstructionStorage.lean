import Blotto.GeneralPaperCatalogueProjectionStorage

/-! Actual catalogue-array constructor. Native cached rows discharge every
projection validity premise; full catalogue/entry-reference buffers coexist
with projected code/fraction/open arrays and the active inner projection row.
The active cached-row constructor is joined separately by the family lemma. -/
namespace Blotto.GeneralPaperCatalogueArrayConstructionStorage
open GeneralPaperCodeAlphabet
open GeneralPaperCatalogueProjection (Field)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def entries {m n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) :=
  (GeneralPaperCachedCatalogueFamily.entries true (fun w => w) W
    (GeneralPaperCatalogueFamilyStorage.nativeFamily model W a response summaries)).1

theorem entries_decoded {m n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) (j : Fin m) (i : Fin (n+2)) :
    (GeneralPaperCodeDecode.decode a response (((entries model W a response summaries).read j).read i).cost).choice=
      some (((entries model W a response summaries).read j).read i).predecessor := by
  unfold entries GeneralPaperCatalogueFamilyStorage.nativeFamily
  rw [GeneralPaperCachedCatalogueFamily.entries_data,FixedArrayTable.read_ofFn,
    GeneralPaperCachedCatalogueFamily.data,FixedArrayTable.read_ofFn]
  exact GeneralPaperCachedCatalogue.decoded a response (summaries.read j) i

theorem arrays_data {m n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) :
    (GeneralPaperCatalogueArraysExecution.run true (fun w => w) model W a response summaries).1=
      (GeneralPaperCatalogueProjection.run true (fun w => w) W (entries model W a response summaries)).1 := rfl

theorem returned {m n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) :
    GeneralPaperEncodedCatalogueStorage.footprint W
      (GeneralPaperCatalogueArraysExecution.run true (fun w => w) model W a response summaries).1≤
      4*(m*(GeneralPaperCatalogueProjectionStorage.rowCapacity W (n+2) a+W)+32*W)+128*W := by
  rw [arrays_data]
  exact GeneralPaperCatalogueProjectionStorage.arrays_returned W a response _ (entries_decoded model W a response summaries)

def window {m n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) (field : Field) (count copied rowCount : ℕ)
    (hc : count≤m) (hd : copied≤m) (hr : rowCount≤n+2) (j : Fin m) : ℕ :=
  let values := entries model W a response summaries
  GeneralPaperCatalogueFamilyStorage.window model W a response summaries count copied hc hd+
    (GeneralPaperCatalogueProjectionStorage.familyWindow W field values count hc+
      GeneralPaperCatalogueProjectionStorage.rowWindow W a field (values.read j) rowCount hr+
      GeneralPaperEncodedCatalogueStorage.footprint W (GeneralPaperCatalogueProjection.run true (fun w => w) W values).1+
      (GeneralPaperCatalogueProjection.run true (fun w => w) W values).2+128*W)+
    (GeneralPaperCatalogueArraysExecution.run true (fun w => w) model W a response summaries).2+128*W

def profile (model : RationalCostModel) (W m n : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperCatalogueFamilyStorage.profile model W m n a+
    (GeneralPaperCatalogueProjectionStorage.familyProfile W m (n+2) a+
      GeneralPaperCatalogueProjectionStorage.rowProfile W (n+2) a+
      4*(m*(GeneralPaperCatalogueProjectionStorage.rowCapacity W (n+2) a+W)+32*W)+128*W+
      GeneralPaperCatalogueProjection.profile W m (n+2)+128*W)+
    GeneralPaperCatalogueArraysExecution.profile model W m n a+128*W

theorem bounded {m n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) (hcodes : ∀ j r,(summaries.read j).read r<2*(8*a.C))
    (field : Field) (count copied rowCount : ℕ) (hc : count≤m) (hd : copied≤m) (hr : rowCount≤n+2) (j : Fin m) :
    window model W a response summaries field count copied rowCount hc hd hr j≤profile model W m n a := by
  have hfamily := GeneralPaperCatalogueFamilyStorage.bounded model W a response summaries hcodes count copied hc hd
  have hprojection := GeneralPaperCatalogueProjectionStorage.with_active_row W a response field
    (entries model W a response summaries) (entries_decoded model W a response summaries) count rowCount hc hr j
  have hwork := GeneralPaperCatalogueArraysExecution.bit_work model W a response summaries hcodes
  unfold window profile
  dsimp only
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hfamily hprojection) hwork) _

theorem with_cached_constructor {m n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) (hcodes : ∀ j r,(summaries.read j).read r<2*(8*a.C))
    (field : Field) (count copied rowCount : ℕ) (hc : count≤m) (hd : copied≤m) (hr : rowCount≤n+2) (j : Fin m)
    (used rowCopied partCount rawCount padCount : ℕ)
    (hp : partCount≤(GeneralPaperCachedCatalogueStorage.part a (summaries.read j)).count)
    (hraw : rawCount≤(GeneralPaperCachedCatalogueStorage.part a (summaries.read j)).count) (hpad : padCount≤n+2) :
    window model W a response summaries field count copied rowCount hc hd hr j+
      GeneralPaperCachedCatalogueStorage.window model W a response (summaries.read j) used rowCopied partCount rawCount padCount hp hraw hpad≤
      profile model W m n a+GeneralPaperCachedCatalogueStorage.profile model W n a :=
  Nat.add_le_add (bounded model W a response summaries hcodes field count copied rowCount hc hd hr j)
    (GeneralPaperCachedCatalogueStorage.bounded model W a response (summaries.read j) (hcodes j)
      used rowCopied partCount rawCount padCount hp hraw hpad)

end Blotto.GeneralPaperCatalogueArrayConstructionStorage
