import Blotto.GeneralPaperCachedCatalogueStorage

/-! Actual outer catalogue and entry-reference fills. All row payloads
include native lookup/padding annotations. Old/new full-capacity buffers and
the complete returned family coexist with one actual cached-row constructor. -/
namespace Blotto.GeneralPaperCatalogueFamilyStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def nativeFamily {m n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) :=
  (GeneralPaperCachedCatalogueFamily.run true (fun w => w) model W a response summaries).1

theorem row_bound {m n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) (j : Fin m) :
    GeneralPaperCachedCatalogueStorage.footprint W ((nativeFamily model W a response summaries).read j)≤
      GeneralPaperCachedCatalogueStorage.recordProfile W n a := by
  unfold nativeFamily
  rw [GeneralPaperCachedCatalogueFamily.data,FixedArrayTable.read_ofFn]
  exact GeneralPaperCachedCatalogueStorage.native W a response (summaries.read j)

def familyPrefix {m n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) (count : ℕ) (hc : count≤m) : ℕ :=
  GeneralPaperEncodedReferenceVector.reservedFootprint W m (GeneralPaperCachedCatalogueStorage.footprint W)
    (PaperIndexedArrayConstruction.fill (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W m)
      (GeneralPaperCachedCatalogueFamily.element true (fun w => w) model W a response summaries) count hc).1

theorem prefix_bound {m n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) (count : ℕ) (hc : count≤m) :
    familyPrefix model W a response summaries count hc≤m*(GeneralPaperCachedCatalogueStorage.recordProfile W n a+W)+64*W :=
  GeneralPaperEncodedReferenceVector.indexed_reserved_prefix (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W m) W
    (GeneralPaperCachedCatalogueStorage.recordProfile W n a) (GeneralPaperCachedCatalogueStorage.footprint W)
    (GeneralPaperCachedCatalogueFamily.element true (fun w => w) model W a response summaries)
    (fun j => GeneralPaperCachedCatalogueStorage.returned model W a response (summaries.read j)) count hc

def entryPrefix {m n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) (count : ℕ) (hc : count≤m) : ℕ :=
  GeneralPaperEncodedReferenceVector.reservedFootprint W m
    (GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedCatalogueStorage.entryBits W))
    (PaperIndexedArrayConstruction.fill (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W m)
      (fun j : Fin m => (((nativeFamily model W a response summaries).read j).entries,32*W)) count hc).1

theorem entry_prefix_bound {m n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) (count : ℕ) (hc : count≤m) :
    entryPrefix model W a response summaries count hc≤m*(GeneralPaperCachedCatalogueStorage.recordProfile W n a+W)+64*W := by
  apply GeneralPaperEncodedReferenceVector.indexed_reserved_prefix (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W m) W
    (GeneralPaperCachedCatalogueStorage.recordProfile W n a)
    (GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedCatalogueStorage.entryBits W))
    (fun j : Fin m => (((nativeFamily model W a response summaries).read j).entries,32*W))
  intro j
  dsimp only
  have h := row_bound model W a response summaries j
  unfold GeneralPaperCachedCatalogueStorage.footprint at h
  omega

def inputFootprint {m n : ℕ} (W : ℕ) (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) : ℕ :=
  GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedNatArray.footprint W) summaries

theorem input_bound {m n : ℕ} (W : ℕ) (a : Alphabet) (summaries : FixedArrayTable m (FixedArrayTable n ℕ))
    (hc : ∀ j r,(summaries.read j).read r<2*(8*a.C)) : inputFootprint W summaries≤
      m*(n*(operandWidth a.lambda+W)+33*W)+32*W := by
  have hsource := GeneralPaperCataloguePartitionStorage.source_payload a
  have hfull : 64+8*a.lambda≤operandWidth a.lambda := by unfold operandWidth; omega
  have hrow (j : Fin m) : GeneralPaperEncodedNatArray.footprint W (summaries.read j)≤n*(operandWidth a.lambda+W)+32*W := by
    apply GeneralPaperEncodedNatArray.bounded_length W (operandWidth a.lambda) n (summaries.read j) (Nat.le_refl _)
    intro r
    have h := Nat.add_le_add_left (binaryWordWidth_mono (hc j r).le) 1
    exact h.trans (hsource.trans hfull)
  have h := GeneralPaperEncodedFixedVector.bounded W (n*(operandWidth a.lambda+W)+32*W)
    (GeneralPaperEncodedNatArray.footprint W) summaries hrow
  exact h.trans_eq (by ring)

def window {m n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) (count copied : ℕ) (hc : count≤m) (hd : copied≤m) : ℕ :=
  inputFootprint W summaries+2*familyPrefix model W a response summaries count hc+
    2*entryPrefix model W a response summaries copied hd+2*GeneralPaperGridArrayConstructionStorage.frames W m+
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperCachedCatalogueStorage.footprint W)
      (nativeFamily model W a response summaries)+
    (GeneralPaperCachedCatalogueFamily.run true (fun w => w) model W a response summaries).2+
    (GeneralPaperCachedCatalogueFamily.entries true (fun w => w) W (nativeFamily model W a response summaries)).2+256*W

def profile (model : RationalCostModel) (W m n : ℕ) (a : Alphabet) : ℕ :=
  m*(n*(operandWidth a.lambda+W)+33*W)+32*W+
    4*(m*(GeneralPaperCachedCatalogueStorage.recordProfile W n a+W)+64*W)+
    2*GeneralPaperGridArrayConstructionStorage.frames W m+
    (m*(GeneralPaperCachedCatalogueStorage.recordProfile W n a+W)+32*W)+
    GeneralPaperCachedCatalogueFamily.profile model W m n a+GeneralPaperCachedCatalogueFamily.entriesProfile W m+256*W

theorem bounded {m n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) (hcodes : ∀ j r,(summaries.read j).read r<2*(8*a.C))
    (count copied : ℕ) (hc : count≤m) (hd : copied≤m) :
    window model W a response summaries count copied hc hd≤profile model W m n a := by
  have hi := input_bound W a summaries hcodes
  have hp := prefix_bound model W a response summaries count hc
  have he := entry_prefix_bound model W a response summaries copied hd
  have hr := GeneralPaperEncodedFixedVector.bounded W (GeneralPaperCachedCatalogueStorage.recordProfile W n a)
    (GeneralPaperCachedCatalogueStorage.footprint W) (nativeFamily model W a response summaries) (row_bound model W a response summaries)
  have hs := GeneralPaperCachedCatalogueFamily.bit_work model W a response summaries hcodes
  have hentries := GeneralPaperCachedCatalogueFamily.entries_bit_work W (nativeFamily model W a response summaries)
  unfold window profile
  omega

theorem with_cached_row {m n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (summaries : FixedArrayTable m (FixedArrayTable n ℕ)) (hcodes : ∀ j r,(summaries.read j).read r<2*(8*a.C))
    (count copied : ℕ) (hc : count≤m) (hd : copied≤m) (j : Fin m)
    (used rowCopied partCount rawCount padCount : ℕ)
    (hp : partCount≤(GeneralPaperCachedCatalogueStorage.part a (summaries.read j)).count)
    (hr : rawCount≤(GeneralPaperCachedCatalogueStorage.part a (summaries.read j)).count) (ht : padCount≤n+2) :
    window model W a response summaries count copied hc hd+
      GeneralPaperCachedCatalogueStorage.window model W a response (summaries.read j) used rowCopied partCount rawCount padCount hp hr ht≤
      profile model W m n a+GeneralPaperCachedCatalogueStorage.profile model W n a :=
  Nat.add_le_add (bounded model W a response summaries hcodes count copied hc hd)
    (GeneralPaperCachedCatalogueStorage.bounded model W a response (summaries.read j) (hcodes j)
      used rowCopied partCount rawCount padCount hp hr ht)

end Blotto.GeneralPaperCatalogueFamilyStorage
