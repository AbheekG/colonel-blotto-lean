import Blotto.GeneralPaperTagValueStorage

/-! Native tag fills reserve full inner/outer capacities and both old/new
buffers. One selected fraction callback coexists with completed tag rows;
original catalogue families remain live throughout preparation. -/
namespace Blotto.GeneralPaperTagFamilyStorage
open GeneralPaperCodeAlphabet
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def rowCapacity (W K lambda : ℕ) : ℕ := K*(GeneralPaperDecoderControls.operandWidth lambda+1+17*W)+32*W

def rowPrefix {K : ℕ} (model : RationalCostModel) (W : ℕ) (thresholds : FixedArrayTable K Farey.Fraction)
    (opened : FixedArrayTable K Bool) (count : ℕ) (hc : count≤K) : ℕ :=
  GeneralPaperEncodedReferenceVector.reservedFootprint W K (GeneralPaperEncodedOptionCache.tagBits W)
    (PaperIndexedArrayConstruction.fill (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W K)
      (GeneralPaperCatalogueTagFamily.entry model.rat W thresholds opened) count hc).1

theorem row_prefix_bound {K : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (thresholds : FixedArrayTable K Farey.Fraction) (opened : FixedArrayTable K Bool)
    (hb : ∀ i,(thresholds.read i).num≤a.C ∧ (thresholds.read i).den≤a.C) (count : ℕ) (hc : count≤K) :
    rowPrefix model W thresholds opened count hc≤rowCapacity W K a.lambda+32*W := by
  have h := GeneralPaperEncodedReferenceVector.indexed_reserved_prefix (fun w => w)
    (GeneralPaperSummaryArrayExecution.arrayWord W K) W (GeneralPaperDecoderControls.operandWidth a.lambda+1+16*W)
    (GeneralPaperEncodedOptionCache.tagBits W) (GeneralPaperCatalogueTagFamily.entry model.rat W thresholds opened)
    (fun i => GeneralPaperTagValueStorage.tag model W a (thresholds.read i) (hb i).1 (hb i).2 (opened.read i)) count hc
  exact h.trans_eq (by unfold rowCapacity; ring)

theorem row_returned {K : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (thresholds : FixedArrayTable K Farey.Fraction) (opened : FixedArrayTable K Bool)
    (hb : ∀ i,(thresholds.read i).num≤a.C ∧ (thresholds.read i).den≤a.C) :
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedOptionCache.tagBits W)
      (GeneralPaperCatalogueTagFamily.row true (fun w => w) model.rat W thresholds opened).1≤rowCapacity W K a.lambda := by
  have h := GeneralPaperEncodedFixedVector.bounded W (GeneralPaperDecoderControls.operandWidth a.lambda+1+16*W)
    (GeneralPaperEncodedOptionCache.tagBits W)
    (GeneralPaperCatalogueTagFamily.row true (fun w => w) model.rat W thresholds opened).1 (by
      intro i
      rw [GeneralPaperCatalogueTagFamily.row_data,FixedArrayTable.read_ofFn]
      exact GeneralPaperTagValueStorage.tag model W a (thresholds.read i) (hb i).1 (hb i).2 (opened.read i))
  exact h.trans_eq (by unfold rowCapacity; ring)

def rowWindow {K : ℕ} (model : RationalCostModel) (W : ℕ) (thresholds : FixedArrayTable K Farey.Fraction)
    (opened : FixedArrayTable K Bool) (count : ℕ) (hc : count≤K) (i : Fin K) : ℕ :=
  GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedCatalogueStorage.fractionBits W) thresholds+
    GeneralPaperEncodedFixedVector.footprint W (fun _ : Bool => 1) opened+
    2*rowPrefix model W thresholds opened count hc+GeneralPaperGridArrayConstructionStorage.frames W K+
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedOptionCache.tagBits W)
      (GeneralPaperCatalogueTagFamily.row true (fun w => w) model.rat W thresholds opened).1+
    GeneralPaperTagValueStorage.window model W (thresholds.read i) (opened.read i)+
    (GeneralPaperCatalogueTagFamily.row true (fun w => w) model.rat W thresholds opened).2+128*W

def rowProfile (model : RationalCostModel) (W K lambda : ℕ) : ℕ :=
  (K*(2*GeneralPaperDecoderControls.operandWidth lambda+17*W)+32*W)+(K*(1+W)+32*W)+
    2*(rowCapacity W K lambda+32*W)+GeneralPaperGridArrayConstructionStorage.frames W K+rowCapacity W K lambda+
    GeneralPaperTagValueStorage.profile model W lambda+GeneralPaperCatalogueTagFamily.rowProfile model W K lambda+128*W

theorem row_bound {K : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (thresholds : FixedArrayTable K Farey.Fraction) (opened : FixedArrayTable K Bool)
    (hb : ∀ i,(thresholds.read i).num≤a.C ∧ (thresholds.read i).den≤a.C) (count : ℕ) (hc : count≤K) (i : Fin K) :
    rowWindow model W thresholds opened count hc i≤rowProfile model W K a.lambda := by
  have hf := GeneralPaperEncodedFixedVector.bounded W (2*GeneralPaperDecoderControls.operandWidth a.lambda+16*W)
    (GeneralPaperEncodedCatalogueStorage.fractionBits W) thresholds (fun i => GeneralPaperTagValueStorage.fraction W a _ (hb i).1 (hb i).2)
  have ho := GeneralPaperEncodedFixedVector.bounded W 1 (fun _ : Bool => 1) opened (fun _ => Nat.le_refl _)
  have hp := row_prefix_bound model W a thresholds opened hb count hc
  have hr := row_returned model W a thresholds opened hb
  have hv := GeneralPaperTagValueStorage.bounded model W a (thresholds.read i) (hb i).1 (hb i).2 (opened.read i)
  have hs := GeneralPaperCatalogueTagFamily.row_bit_work model W a thresholds opened hb
  have hf' : GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedCatalogueStorage.fractionBits W) thresholds≤
      K*(2*GeneralPaperDecoderControls.operandWidth a.lambda+17*W)+32*W := hf.trans_eq (by ring)
  unfold rowWindow rowProfile
  omega

def familyPrefix {m K : ℕ} (model : RationalCostModel) (W : ℕ) (data : GeneralPaperCatalogueArrays.Arrays m K)
    (count : ℕ) (hc : count≤m) : ℕ :=
  GeneralPaperEncodedReferenceVector.reservedFootprint W m
    (GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedOptionCache.tagBits W))
    (PaperIndexedArrayConstruction.fill (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W m)
      (GeneralPaperCatalogueTagFamily.element true (fun w => w) model.rat W data) count hc).1

theorem family_prefix_bound {m K : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (data : GeneralPaperCatalogueArrays.Arrays m K)
    (hb : ∀ j i,((data.thresholds.read j).read i).num≤a.C ∧ ((data.thresholds.read j).read i).den≤a.C)
    (count : ℕ) (hc : count≤m) : familyPrefix model W data count hc≤m*(rowCapacity W K a.lambda+W)+64*W :=
  GeneralPaperEncodedReferenceVector.indexed_reserved_prefix (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W m) W
    (rowCapacity W K a.lambda) (GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedOptionCache.tagBits W))
    (GeneralPaperCatalogueTagFamily.element true (fun w => w) model.rat W data)
    (fun j => row_returned model W a (data.thresholds.read j) (data.opened.read j) (hb j)) count hc

theorem family_returned {m K : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (data : GeneralPaperCatalogueArrays.Arrays m K)
    (hb : ∀ j i,((data.thresholds.read j).read i).num≤a.C ∧ ((data.thresholds.read j).read i).den≤a.C) :
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedOptionCache.tagBits W))
      (GeneralPaperCatalogueTagFamily.run true (fun w => w) model.rat W data).1≤m*(rowCapacity W K a.lambda+W)+32*W := by
  apply GeneralPaperEncodedFixedVector.bounded W (rowCapacity W K a.lambda)
  intro j
  rw [GeneralPaperCatalogueTagFamily.data]
  unfold GeneralPaperCatalogueArrays.tags GeneralPaperNativeRowBudget.tags
  rw [FixedArrayTable.read_ofFn]
  change GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedOptionCache.tagBits W)
    (FixedArrayTable.ofFn (fun i => (⟨((data.thresholds.read j).read i).value,(data.opened.read j).read i⟩:GeneralPaperResponseTag.Tag)))≤_
  have h := row_returned model W a (data.thresholds.read j) (data.opened.read j) (hb j)
  rw [GeneralPaperCatalogueTagFamily.row_data] at h
  exact h

theorem with_active_row {m k : ℕ} (model : RationalCostModel) (W : ℕ) (ready : GeneralPaperCatalogueOptimizer.Ready m k)
    (count rowCount : ℕ) (hc : count≤m) (hr : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) :
    GeneralPaperEncodedCatalogueStorage.footprint W ready.data+2*familyPrefix model W ready.data count hc+
      GeneralPaperGridArrayConstructionStorage.frames W m+
      GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedOptionCache.tagBits W))
        (GeneralPaperCatalogueTagFamily.run true (fun w => w) model.rat W ready.data).1+
      rowWindow model W (ready.data.thresholds.read j) (ready.data.opened.read j) rowCount hr i+
      (GeneralPaperCatalogueTagFamily.run true (fun w => w) model.rat W ready.data).2+128*W≤
    GeneralPaperEncodedCatalogueStorage.profile W m ((GeneralPaperSourceParameters.prepare k).summarySize+2)
        (GeneralPaperDecoderControls.operandWidth ready.alphabet.lambda)+
      2*(m*(rowCapacity W ((GeneralPaperSourceParameters.prepare k).summarySize+2) ready.alphabet.lambda+W)+64*W)+
      GeneralPaperGridArrayConstructionStorage.frames W m+
      (m*(rowCapacity W ((GeneralPaperSourceParameters.prepare k).summarySize+2) ready.alphabet.lambda+W)+32*W)+
      rowProfile model W ((GeneralPaperSourceParameters.prepare k).summarySize+2) ready.alphabet.lambda+
      GeneralPaperCatalogueTagFamily.profile model W m ((GeneralPaperSourceParameters.prepare k).summarySize+2) ready.alphabet.lambda+128*W := by
  have hb := GeneralPaperCatalogueTagValue.native_bounds ready.alphabet ready.response k ready.summaries ready.data ready.data_spec
  have hd := GeneralPaperEncodedCatalogueStorage.ready_data W ready
  have hp := family_prefix_bound model W ready.alphabet ready.data hb count hc
  have hf := family_returned model W ready.alphabet ready.data hb
  have hrow := row_bound model W ready.alphabet (ready.data.thresholds.read j) (ready.data.opened.read j) (hb j) rowCount hr i
  have hs := GeneralPaperCatalogueTagFamily.bit_work model W ready.alphabet ready.data hb
  omega

def familyWindow {m K : ℕ} (model : RationalCostModel) (W : ℕ) (data : GeneralPaperCatalogueArrays.Arrays m K)
    (count rowCount : ℕ) (hc : count≤m) (hr : rowCount≤K) (j : Fin m) (i : Fin K) : ℕ :=
  GeneralPaperEncodedCatalogueStorage.footprint W data+2*familyPrefix model W data count hc+
    GeneralPaperGridArrayConstructionStorage.frames W m+
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedOptionCache.tagBits W))
      (GeneralPaperCatalogueTagFamily.run true (fun w => w) model.rat W data).1+
    rowWindow model W (data.thresholds.read j) (data.opened.read j) rowCount hr i+
    (GeneralPaperCatalogueTagFamily.run true (fun w => w) model.rat W data).2+128*W

def familyProfile (model : RationalCostModel) (W m K lambda : ℕ) : ℕ :=
  GeneralPaperEncodedCatalogueStorage.profile W m K (GeneralPaperDecoderControls.operandWidth lambda)+
    2*(m*(rowCapacity W K lambda+W)+64*W)+GeneralPaperGridArrayConstructionStorage.frames W m+
    (m*(rowCapacity W K lambda+W)+32*W)+rowProfile model W K lambda+
    GeneralPaperCatalogueTagFamily.profile model W m K lambda+128*W

theorem family_bound {m k : ℕ} (model : RationalCostModel) (W : ℕ) (ready : GeneralPaperCatalogueOptimizer.Ready m k)
    (count rowCount : ℕ) (hc : count≤m) (hr : rowCount≤(GeneralPaperSourceParameters.prepare k).summarySize+2)
    (j : Fin m) (i : Fin ((GeneralPaperSourceParameters.prepare k).summarySize+2)) :
    familyWindow model W ready.data count rowCount hc hr j i≤
      familyProfile model W m ((GeneralPaperSourceParameters.prepare k).summarySize+2) ready.alphabet.lambda :=
  with_active_row model W ready count rowCount hc hr j i

end Blotto.GeneralPaperTagFamilyStorage
