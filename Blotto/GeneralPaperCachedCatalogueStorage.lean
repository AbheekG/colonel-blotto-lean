import Blotto.GeneralPaperCataloguePaddingStorage

/-! Complete cached catalogue: actual source partition, raw and padded
construction windows, whole returned entries and both retained native work
fields. Every raw validity/count/endpoint premise is discharged natively. -/
namespace Blotto.GeneralPaperCachedCatalogueStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def footprint {cap : ℕ} (W : ℕ) (c : GeneralPaperCachedCatalogue.Prepared cap) : ℕ :=
  GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedCatalogueStorage.entryBits W) c.entries+
    fields W [c.lookupWork,c.paddingWork]+64*W

def recordProfile (W n : ℕ) (a : Alphabet) : ℕ :=
  (n+2)*(GeneralPaperCataloguePaddingStorage.entryCapacity W a.lambda+W)+32*W+
    2*(GeneralPaperCellCatalogueOperands.width (n+1) a.lambda+GeneralPaperCatalogueSlotsPrice.width (n+1)+W)+96*W

theorem native (W : ℕ) (a : Alphabet) (response : Bool) {n : ℕ} (summary : FixedArrayTable n ℕ) :
    footprint W (GeneralPaperCachedCatalogue.prepare a response summary)≤recordProfile W n a := by
  let c := GeneralPaperCachedCatalogue.prepare a response summary
  have he := GeneralPaperEncodedFixedVector.bounded W (GeneralPaperCataloguePaddingStorage.entryCapacity W a.lambda)
    (GeneralPaperEncodedCatalogueStorage.entryBits W) c.entries (by
      intro i
      exact GeneralPaperCodeRecordStorage.entry W a response _ (GeneralPaperCachedCatalogue.decoded a response summary i))
  change _≤(n+2)*(GeneralPaperCataloguePaddingStorage.entryCapacity W a.lambda+W)+32*W at he
  have hl := GeneralPaperCachedCatalogue.lookup_work a response summary
  have hcap := GeneralPaperCellCatalogueOperands.annotation_cap (n+1) a.lambda (n+1) (Nat.le_refl _)
  have hlookup : natBits c.lookupWork≤GeneralPaperCellCatalogueOperands.width (n+1) a.lambda :=
    (Nat.add_le_add_left (binaryWordWidth_mono (hl.trans hcap)) 1).trans
      (GeneralPaperCellCatalogueOperands.word_bound (n+1) a.lambda)
  have hp := GeneralPaperCataloguePaddingStorage.annotation_word (n+1)
  have hpadding : natBits c.paddingWork≤GeneralPaperCatalogueSlotsPrice.width (n+1) := by
    dsimp only [c]
    rw [GeneralPaperCachedCatalogue.padding_work]
    exact hp
  have hf := fields_bound W (GeneralPaperCellCatalogueOperands.width (n+1) a.lambda+GeneralPaperCatalogueSlotsPrice.width (n+1))
    [c.lookupWork,c.paddingWork] (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl <;> omega)
  change _≤2*(GeneralPaperCellCatalogueOperands.width (n+1) a.lambda+GeneralPaperCatalogueSlotsPrice.width (n+1)+W)+32*W at hf
  unfold footprint recordProfile
  change GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedCatalogueStorage.entryBits W) c.entries+
    fields W [c.lookupWork,c.paddingWork]+64*W≤_
  omega

theorem returned {n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (summary : FixedArrayTable n ℕ) :
    footprint W (GeneralPaperCachedCatalogueExecution.run true (fun w => w) model W a response summary).1≤recordProfile W n a := by
  rw [GeneralPaperCachedCatalogueExecution.data]
  exact native W a response summary

def part {n : ℕ} (a : Alphabet) (summary : FixedArrayTable n ℕ) : GeneralPaperPreparedPartition.Prepared :=
  GeneralPaperTailCataloguePartition.prepare (8*a.C) summary

def raw {n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (summary : FixedArrayTable n ℕ) :=
  (GeneralPaperCellCatalogueExecution.run true (fun w => w) model W a response (part a summary).intervals).1.1

theorem raw_sound {n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (summary : FixedArrayTable n ℕ) :
    ∀ r e,(raw model W a response summary).read r=some e →
      (GeneralPaperCodeDecode.decode a response e.cost).choice=some e.predecessor := by
  intro r e he
  exact (GeneralPaperCellCatalogueData.sound true (fun w => w) model W a response (part a summary).intervals r e he).2

theorem part_bounds {n : ℕ} (a : Alphabet) (summary : FixedArrayTable n ℕ) :
    ∀ r,((part a summary).intervals.read r).1≤8*a.C ∧ ((part a summary).intervals.read r).2≤8*a.C := by
  intro r
  exact GeneralPaperActualEpochInstructions.bounds_of_build (8*a.C)
    (GeneralPaperTailCataloguePartition.points (8*a.C) summary) (part a summary) rfl r

def metadata (W n : ℕ) (a : Alphabet) : ℕ := fields W [8,a.C,8*a.C,n,n+1]

theorem metadata_bound (W n : ℕ) (a : Alphabet) : metadata W n a≤
    5*(operandWidth a.lambda+natBits (n+1)+W)+32*W := by
  have hC := a.scalePositive
  have h0 := code_word a 8 (by omega)
  have h1 := code_word a a.C (by omega)
  have h2 := code_word a (8*a.C) (Nat.le_refl _)
  have hn := binaryWordWidth_mono (show n≤n+1 by omega)
  apply fields_bound W (operandWidth a.lambda+natBits (n+1))
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with hx|hx|hx|hx|hx <;> rw [hx] <;> unfold natBits at * <;> omega

def window {n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (summary : FixedArrayTable n ℕ)
    (used copied partCount rawCount padCount : ℕ)
    (hp : partCount≤(part a summary).count) (hr : rawCount≤(part a summary).count) (hd : padCount≤n+2) : ℕ :=
  GeneralPaperCataloguePartitionStorage.window model W (8*a.C) used copied partCount summary hp+
    GeneralPaperRawCatalogueConstructionStorage.window model W a response (part a summary).intervals rawCount hr+
    GeneralPaperCataloguePaddingStorage.window model W a (raw model W a response summary) padCount hd+
    footprint W (GeneralPaperCachedCatalogueExecution.run true (fun w => w) model W a response summary).1+
    metadata W n a+(GeneralPaperCachedCatalogueExecution.run true (fun w => w) model W a response summary).2+256*W

def profile (model : RationalCostModel) (W n : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperCataloguePartitionStorage.profile model W (8*a.C) n+
    GeneralPaperRawCatalogueConstructionStorage.profile model W (n+1) a+
    GeneralPaperCataloguePaddingStorage.profile model W (n+1) a+recordProfile W n a+
    5*(operandWidth a.lambda+natBits (n+1)+W)+32*W+
      GeneralPaperCachedCataloguePrice.profile model W n a+256*W

theorem bounded {n : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool) (summary : FixedArrayTable n ℕ)
    (hcodes : ∀ r,summary.read r<2*(8*a.C)) (used copied partCount rawCount padCount : ℕ)
    (hp : partCount≤(part a summary).count) (hr : rawCount≤(part a summary).count) (hd : padCount≤n+2) :
    window model W a response summary used copied partCount rawCount padCount hp hr hd≤profile model W n a := by
  have hCount : (part a summary).count≤n+1 := GeneralPaperTailCataloguePartition.count_bound (8*a.C) summary
  have hpart := GeneralPaperCataloguePartitionStorage.bounded model W (8*a.C) used copied partCount summary hp hcodes
  have hraw := (GeneralPaperRawCatalogueConstructionStorage.bounded model W a response (part a summary).intervals
    (part_bounds a summary) rawCount hr).trans (GeneralPaperRawCatalogueConstructionStorage.profile_mono model W _ (n+1) a hCount)
  have hpad := GeneralPaperCataloguePaddingStorage.bounded (cap:=n+1) model W a response
    (raw model W a response summary) hCount (raw_sound model W a response summary) padCount hd
  have hreturn := returned model W a response summary
  have hm := metadata_bound W n a
  have hs := GeneralPaperCachedCataloguePrice.bit_work model W a response summary hcodes
  unfold window profile
  omega

end Blotto.GeneralPaperCachedCatalogueStorage
