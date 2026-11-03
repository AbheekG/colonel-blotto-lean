import Blotto.GeneralPaperCatalogueFamilyStorage

/-! Native catalogue reference projections own all constructed inner/outer
slots in this conservative observer. Original entry payloads, each completed
family and one active inner row coexist; no catalogue or decoder is replayed. -/
namespace Blotto.GeneralPaperCatalogueProjectionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet
open GeneralPaperCatalogueProjection (Field FieldType select)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def encode (W : ℕ) : (field : Field) → FieldType field → ℕ
  | .code => GeneralPaperEncodedCatalogueStorage.codeBits
  | .threshold => GeneralPaperEncodedCatalogueStorage.fractionBits W
  | .opened => fun _ => 1

theorem select_bound (W : ℕ) (field : Field) (e : GeneralPaperCodeMinimumScan.Entry) :
    encode W field (select field e)≤GeneralPaperEncodedCatalogueStorage.entryBits W e := by
  cases field <;> dsimp only [encode,select] <;> unfold GeneralPaperEncodedCatalogueStorage.entryBits <;> omega

def rowCapacity (W K : ℕ) (a : Alphabet) : ℕ := K*(GeneralPaperCataloguePaddingStorage.entryCapacity W a.lambda+W)+32*W

def rowPrefix {K : ℕ} (W : ℕ) (field : Field) (values : FixedArrayTable K GeneralPaperCodeMinimumScan.Entry)
    (count : ℕ) (hc : count≤K) : ℕ :=
  GeneralPaperEncodedReferenceVector.reservedFootprint W K (encode W field)
    (PaperIndexedArrayConstruction.fill (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W K)
      (fun i : Fin K => (select field (values.read i),32*W)) count hc).1

theorem row_prefix_bound {K : ℕ} (W : ℕ) (a : Alphabet) (response : Bool) (field : Field)
    (values : FixedArrayTable K GeneralPaperCodeMinimumScan.Entry)
    (hd : ∀ i,(GeneralPaperCodeDecode.decode a response (values.read i).cost).choice=some (values.read i).predecessor)
    (count : ℕ) (hc : count≤K) : rowPrefix W field values count hc≤
      K*(GeneralPaperCataloguePaddingStorage.entryCapacity W a.lambda+W)+64*W := by
  apply GeneralPaperEncodedReferenceVector.indexed_reserved_prefix (fun w => w)
    (GeneralPaperSummaryArrayExecution.arrayWord W K) W (GeneralPaperCataloguePaddingStorage.entryCapacity W a.lambda)
    (encode W field) (fun i : Fin K => (select field (values.read i),32*W))
  intro i
  exact (select_bound W field (values.read i)).trans (GeneralPaperCodeRecordStorage.entry W a response _ (hd i))

theorem row_returned {K : ℕ} (W : ℕ) (a : Alphabet) (response : Bool) (field : Field)
    (values : FixedArrayTable K GeneralPaperCodeMinimumScan.Entry)
    (hd : ∀ i,(GeneralPaperCodeDecode.decode a response (values.read i).cost).choice=some (values.read i).predecessor) :
    GeneralPaperEncodedFixedVector.footprint W (encode W field)
      (GeneralPaperCatalogueProjection.row true (fun w => w) W field values).1≤rowCapacity W K a := by
  apply GeneralPaperEncodedFixedVector.bounded W (GeneralPaperCataloguePaddingStorage.entryCapacity W a.lambda)
  intro i
  rw [GeneralPaperCatalogueProjection.row_data,FixedArrayTable.read_ofFn]
  exact (select_bound W field (values.read i)).trans (GeneralPaperCodeRecordStorage.entry W a response _ (hd i))

def rowWindow {K : ℕ} (W : ℕ) (a : Alphabet) (field : Field) (values : FixedArrayTable K GeneralPaperCodeMinimumScan.Entry)
    (count : ℕ) (hc : count≤K) : ℕ :=
  GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedCatalogueStorage.entryBits W) values+
    2*rowPrefix W field values count hc+GeneralPaperGridArrayConstructionStorage.frames W K+
    GeneralPaperEncodedFixedVector.footprint W (encode W field)
      (GeneralPaperCatalogueProjection.row true (fun w => w) W field values).1+
    GeneralPaperCataloguePaddingStorage.entryCapacity W a.lambda+
    (GeneralPaperCatalogueProjection.row true (fun w => w) W field values).2+128*W

def rowProfile (W K : ℕ) (a : Alphabet) : ℕ :=
  rowCapacity W K a+2*(K*(GeneralPaperCataloguePaddingStorage.entryCapacity W a.lambda+W)+64*W)+
    GeneralPaperGridArrayConstructionStorage.frames W K+rowCapacity W K a+
    GeneralPaperCataloguePaddingStorage.entryCapacity W a.lambda+GeneralPaperCatalogueProjection.rowProfile W K+128*W

theorem row_bound {K : ℕ} (W : ℕ) (a : Alphabet) (response : Bool) (field : Field)
    (values : FixedArrayTable K GeneralPaperCodeMinimumScan.Entry)
    (hd : ∀ i,(GeneralPaperCodeDecode.decode a response (values.read i).cost).choice=some (values.read i).predecessor)
    (count : ℕ) (hc : count≤K) : rowWindow W a field values count hc≤rowProfile W K a := by
  have hi := GeneralPaperEncodedFixedVector.bounded W (GeneralPaperCataloguePaddingStorage.entryCapacity W a.lambda)
    (GeneralPaperEncodedCatalogueStorage.entryBits W) values (fun i => GeneralPaperCodeRecordStorage.entry W a response _ (hd i))
  change _≤rowCapacity W K a at hi
  have hp := row_prefix_bound W a response field values hd count hc
  have hr := row_returned W a response field values hd
  have hs := GeneralPaperCatalogueProjection.row_bit_work W field values
  unfold rowWindow rowProfile
  omega

def familyPrefix {m K : ℕ} (W : ℕ) (field : Field) (values : FixedArrayTable m (FixedArrayTable K GeneralPaperCodeMinimumScan.Entry))
    (count : ℕ) (hc : count≤m) : ℕ :=
  GeneralPaperEncodedReferenceVector.reservedFootprint W m (GeneralPaperEncodedFixedVector.footprint W (encode W field))
    (PaperIndexedArrayConstruction.fill (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W m)
      (GeneralPaperCatalogueProjection.element true (fun w => w) W field values) count hc).1

theorem family_prefix_bound {m K : ℕ} (W : ℕ) (a : Alphabet) (response : Bool) (field : Field)
    (values : FixedArrayTable m (FixedArrayTable K GeneralPaperCodeMinimumScan.Entry))
    (hd : ∀ j i,(GeneralPaperCodeDecode.decode a response ((values.read j).read i).cost).choice=some ((values.read j).read i).predecessor)
    (count : ℕ) (hc : count≤m) : familyPrefix W field values count hc≤m*(rowCapacity W K a+W)+64*W :=
  GeneralPaperEncodedReferenceVector.indexed_reserved_prefix (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W m) W
    (rowCapacity W K a) (GeneralPaperEncodedFixedVector.footprint W (encode W field))
    (GeneralPaperCatalogueProjection.element true (fun w => w) W field values)
    (fun j => row_returned W a response field (values.read j) (hd j)) count hc

theorem family_returned {m K : ℕ} (W : ℕ) (a : Alphabet) (response : Bool) (field : Field)
    (values : FixedArrayTable m (FixedArrayTable K GeneralPaperCodeMinimumScan.Entry))
    (hd : ∀ j i,(GeneralPaperCodeDecode.decode a response ((values.read j).read i).cost).choice=some ((values.read j).read i).predecessor) :
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedFixedVector.footprint W (encode W field))
      (GeneralPaperCatalogueProjection.family true (fun w => w) W field values).1≤m*(rowCapacity W K a+W)+32*W := by
  apply GeneralPaperEncodedFixedVector.bounded W (rowCapacity W K a)
  intro j
  rw [GeneralPaperCatalogueProjection.family_data,FixedArrayTable.read_ofFn]
  have h := row_returned W a response field (values.read j) (hd j)
  rw [GeneralPaperCatalogueProjection.row_data] at h
  exact h

def inputFootprint {m K : ℕ} (W : ℕ) (values : FixedArrayTable m (FixedArrayTable K GeneralPaperCodeMinimumScan.Entry)) : ℕ :=
  GeneralPaperEncodedFixedVector.footprint W
    (GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedCatalogueStorage.entryBits W)) values

theorem input_bound {m K : ℕ} (W : ℕ) (a : Alphabet) (response : Bool)
    (values : FixedArrayTable m (FixedArrayTable K GeneralPaperCodeMinimumScan.Entry))
    (hd : ∀ j i,(GeneralPaperCodeDecode.decode a response ((values.read j).read i).cost).choice=some ((values.read j).read i).predecessor) :
    inputFootprint W values≤m*(rowCapacity W K a+W)+32*W := by
  apply GeneralPaperEncodedFixedVector.bounded W (rowCapacity W K a)
  intro j
  exact GeneralPaperEncodedFixedVector.bounded W (GeneralPaperCataloguePaddingStorage.entryCapacity W a.lambda)
    (GeneralPaperEncodedCatalogueStorage.entryBits W) (values.read j) (fun i => GeneralPaperCodeRecordStorage.entry W a response _ (hd j i))

def familyWindow {m K : ℕ} (W : ℕ) (field : Field)
    (values : FixedArrayTable m (FixedArrayTable K GeneralPaperCodeMinimumScan.Entry)) (count : ℕ) (hc : count≤m) : ℕ :=
  inputFootprint W values+2*familyPrefix W field values count hc+GeneralPaperGridArrayConstructionStorage.frames W m+
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedFixedVector.footprint W (encode W field))
      (GeneralPaperCatalogueProjection.family true (fun w => w) W field values).1+
    (GeneralPaperCatalogueProjection.family true (fun w => w) W field values).2+128*W

def familyProfile (W m K : ℕ) (a : Alphabet) : ℕ :=
  (m*(rowCapacity W K a+W)+32*W)+2*(m*(rowCapacity W K a+W)+64*W)+
    GeneralPaperGridArrayConstructionStorage.frames W m+(m*(rowCapacity W K a+W)+32*W)+
    GeneralPaperCatalogueProjection.familyProfile W m K+128*W

theorem family_bound {m K : ℕ} (W : ℕ) (a : Alphabet) (response : Bool) (field : Field)
    (values : FixedArrayTable m (FixedArrayTable K GeneralPaperCodeMinimumScan.Entry))
    (hd : ∀ j i,(GeneralPaperCodeDecode.decode a response ((values.read j).read i).cost).choice=some ((values.read j).read i).predecessor)
    (count : ℕ) (hc : count≤m) : familyWindow W field values count hc≤familyProfile W m K a := by
  have hi := input_bound W a response values hd
  have hp := family_prefix_bound W a response field values hd count hc
  have hr := family_returned W a response field values hd
  have hs := GeneralPaperCatalogueProjection.family_bit_work W field values
  unfold familyWindow familyProfile
  omega

theorem arrays_returned {m K : ℕ} (W : ℕ) (a : Alphabet) (response : Bool)
    (values : FixedArrayTable m (FixedArrayTable K GeneralPaperCodeMinimumScan.Entry))
    (hd : ∀ j i,(GeneralPaperCodeDecode.decode a response ((values.read j).read i).cost).choice=some ((values.read j).read i).predecessor) :
    GeneralPaperEncodedCatalogueStorage.footprint W (GeneralPaperCatalogueProjection.run true (fun w => w) W values).1≤
      4*(m*(rowCapacity W K a+W)+32*W)+128*W := by
  have he := input_bound W a response values hd
  have hc := family_returned W a response .code values hd
  have ht := family_returned W a response .threshold values hd
  have ho := family_returned W a response .opened values hd
  unfold GeneralPaperEncodedCatalogueStorage.footprint GeneralPaperCatalogueProjection.run
  dsimp only
  unfold inputFootprint at he
  dsimp only [encode,FieldType] at hc ht ho ⊢
  omega

theorem with_active_row {m K : ℕ} (W : ℕ) (a : Alphabet) (response : Bool) (field : Field)
    (values : FixedArrayTable m (FixedArrayTable K GeneralPaperCodeMinimumScan.Entry))
    (hd : ∀ j i,(GeneralPaperCodeDecode.decode a response ((values.read j).read i).cost).choice=some ((values.read j).read i).predecessor)
    (count rowCount : ℕ) (hc : count≤m) (hr : rowCount≤K) (j : Fin m) :
    familyWindow W field values count hc+rowWindow W a field (values.read j) rowCount hr+
      GeneralPaperEncodedCatalogueStorage.footprint W (GeneralPaperCatalogueProjection.run true (fun w => w) W values).1+
      (GeneralPaperCatalogueProjection.run true (fun w => w) W values).2+128*W≤
      familyProfile W m K a+rowProfile W K a+4*(m*(rowCapacity W K a+W)+32*W)+128*W+
      GeneralPaperCatalogueProjection.profile W m K+128*W := by
  have hf := family_bound W a response field values hd count hc
  have hrow := row_bound W a response field (values.read j) (hd j) rowCount hr
  have houtput := arrays_returned W a response values hd
  have hs := GeneralPaperCatalogueProjection.bit_work W values
  omega

end Blotto.GeneralPaperCatalogueProjectionStorage
