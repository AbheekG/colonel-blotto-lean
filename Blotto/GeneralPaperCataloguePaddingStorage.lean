import Blotto.GeneralPaperRawCatalogueConstructionStorage

/-! Native catalogue padding: fallback/selected entries, fully reserved old
and new arrays, structural index frames and the actual closed-form native
work annotation. Native raw lookup soundness discharges the entry premise. -/
namespace Blotto.GeneralPaperCataloguePaddingStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet GeneralPaperDecoderControls
open GeneralPaperCodeMinimumScan (Entry)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def entryCapacity (W lambda : ℕ) : ℕ := 3*operandWidth lambda+48*W+1

theorem element_bound {n cap : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (raw : FixedArrayTable n (Option Entry))
    (hs : ∀ r e,raw.read r=some e → (GeneralPaperCodeDecode.decode a response e.cost).choice=some e.predecessor)
    (i : Fin (cap+1)) :
    GeneralPaperEncodedCatalogueStorage.entryBits W
      (GeneralPaperCatalogueSlotsExecution.element model.rat W (GeneralPaperCatalogueSlots.zero a) raw i).1≤entryCapacity W a.lambda := by
  rw [GeneralPaperCatalogueSlotsExecution.element_data]
  have h := GeneralPaperCatalogueSlots.decoded a response raw hs i
  rw [GeneralPaperCatalogueSlots.read_build] at h
  exact GeneralPaperCodeRecordStorage.entry W a response _ h

def filledPrefix {n cap : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (raw : FixedArrayTable n (Option Entry)) (count : ℕ) (hc : count≤cap+1) : ℕ :=
  GeneralPaperEncodedReferenceVector.reservedFootprint W (cap+1) (GeneralPaperEncodedCatalogueStorage.entryBits W)
    (PaperIndexedArrayConstruction.fill (fun w => w) (GeneralPaperSummaryArrayExecution.arrayWord W (cap+1))
      (GeneralPaperCatalogueSlotsExecution.element (cap:=cap) model.rat W (GeneralPaperCatalogueSlots.zero a) raw) count hc).1

theorem prefix_bound {n cap : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (raw : FixedArrayTable n (Option Entry))
    (hs : ∀ r e,raw.read r=some e → (GeneralPaperCodeDecode.decode a response e.cost).choice=some e.predecessor)
    (count : ℕ) (hc : count≤cap+1) : filledPrefix model W a raw count hc≤
      (cap+1)*(entryCapacity W a.lambda+W)+64*W :=
  GeneralPaperEncodedReferenceVector.indexed_reserved_prefix (fun w => w)
    (GeneralPaperSummaryArrayExecution.arrayWord W (cap+1)) W (entryCapacity W a.lambda)
    (GeneralPaperEncodedCatalogueStorage.entryBits W)
    (GeneralPaperCatalogueSlotsExecution.element (cap:=cap) model.rat W (GeneralPaperCatalogueSlots.zero a) raw)
    (element_bound model W a response raw hs) count hc

theorem annotation_word (cap : ℕ) : natBits (62*(cap+1)+18)≤GeneralPaperCatalogueSlotsPrice.width cap :=
  GeneralPaperCatalogueSlotsPrice.bounded_word cap _ (by unfold GeneralPaperCatalogueSlotsPrice.magnitude; omega)

def controls (W n cap count : ℕ) : ℕ :=
  fields W [n,cap,cap+1,count,count-1,62*(cap+1),62*(cap+1)+18]+64*W

theorem controls_bound (W n cap count : ℕ) (hn : n≤cap) (hc : count≤cap+1) :
    controls W n cap count≤7*GeneralPaperCatalogueSlotsPrice.width cap+103*W := by
  have h := fields_bound W (GeneralPaperCatalogueSlotsPrice.width cap)
    [n,cap,cap+1,count,count-1,62*(cap+1),62*(cap+1)+18] (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with hx|hx|hx|hx|hx|hx|hx <;> rw [hx] <;>
        apply GeneralPaperCatalogueSlotsPrice.bounded_word <;> unfold GeneralPaperCatalogueSlotsPrice.magnitude <;> omega)
  change _≤7*(GeneralPaperCatalogueSlotsPrice.width cap+W)+32*W at h
  unfold controls
  omega

def framePeak (W n cap : ℕ) : ℕ → ℕ
  | 0 => controls W n cap 0+128*W
  | count+1 => controls W n cap (count+1)+128*W+framePeak W n cap count

theorem frames_bound (W n cap count : ℕ) (hn : n≤cap) (hc : count≤cap+1) :
    framePeak W n cap count≤(cap+2)*(8*GeneralPaperCatalogueSlotsPrice.width cap+256*W) := by
  have h (used : ℕ) (hu : used≤cap+1) :
      framePeak W n cap used≤(used+1)*(8*GeneralPaperCatalogueSlotsPrice.width cap+256*W) := by
    induction used with
    | zero =>
      have hf := controls_bound W n cap 0 hn (by omega)
      unfold framePeak
      omega
    | succ used ih =>
      have hf := controls_bound W n cap (used+1) hn hu
      have hi := ih (by omega)
      rw [framePeak]
      nlinarith only [hf,hi]
  exact (h count hc).trans (Nat.mul_le_mul_right _ (by omega))

def currentEntry {n cap : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (raw : FixedArrayTable n (Option Entry)) (count : ℕ) : Entry :=
  if h : count<cap+1 then
    (GeneralPaperCatalogueSlotsExecution.element (cap:=cap) model.rat W (GeneralPaperCatalogueSlots.zero a) raw ⟨count,h⟩).1
  else GeneralPaperCatalogueSlots.zero a

theorem current_bound {n cap : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (raw : FixedArrayTable n (Option Entry))
    (hs : ∀ r e,raw.read r=some e → (GeneralPaperCodeDecode.decode a response e.cost).choice=some e.predecessor) (count : ℕ) :
    GeneralPaperEncodedCatalogueStorage.entryBits W (currentEntry (cap:=cap) model W a raw count)≤entryCapacity W a.lambda := by
  unfold currentEntry
  split
  · exact element_bound model W a response raw hs _
  · exact GeneralPaperCodeRecordStorage.entry W a response _ (GeneralPaperCodeDecodeSound.decode_zero a response)

theorem returned {n cap : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (raw : FixedArrayTable n (Option Entry))
    (hs : ∀ r e,raw.read r=some e → (GeneralPaperCodeDecode.decode a response e.cost).choice=some e.predecessor) :
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedCatalogueStorage.entryBits W)
      (GeneralPaperCatalogueSlotsExecution.run (cap:=cap) true (fun w => w) model W a raw).1.1≤
      (cap+1)*(entryCapacity W a.lambda+W)+32*W := by
  rw [GeneralPaperCatalogueSlotsExecution.array_data]
  apply GeneralPaperEncodedFixedVector.bounded W (entryCapacity W a.lambda)
  intro i
  exact GeneralPaperCodeRecordStorage.entry W a response _ (GeneralPaperCatalogueSlots.decoded a response raw hs i)

def window {n cap : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (raw : FixedArrayTable n (Option Entry)) (count : ℕ) (hc : count≤cap+1) : ℕ :=
  GeneralPaperEncodedFixedVector.footprint W (GeneralPaperCodeRecordStorage.optionalEntry W) raw+
    2*filledPrefix model W a raw count hc+framePeak W n cap count+
    GeneralPaperEncodedCatalogueStorage.entryBits W (GeneralPaperCatalogueSlots.zero a)+
    GeneralPaperEncodedCatalogueStorage.entryBits W (currentEntry (cap:=cap) model W a raw count)+
    GeneralPaperEncodedFixedVector.footprint W (GeneralPaperEncodedCatalogueStorage.entryBits W)
      (GeneralPaperCatalogueSlotsExecution.run (cap:=cap) true (fun w => w) model W a raw).1.1+
    natBits (GeneralPaperCatalogueSlotsExecution.run (cap:=cap) true (fun w => w) model W a raw).1.2+
    (GeneralPaperCatalogueSlotsExecution.run (cap:=cap) true (fun w => w) model W a raw).2+256*W

def profile (model : RationalCostModel) (W cap : ℕ) (a : Alphabet) : ℕ :=
  cap*(GeneralPaperRawCatalogueStorage.entryCapacity W a.lambda+W)+32*W+
    2*((cap+1)*(entryCapacity W a.lambda+W)+64*W)+(cap+2)*(8*GeneralPaperCatalogueSlotsPrice.width cap+256*W)+
    2*entryCapacity W a.lambda+((cap+1)*(entryCapacity W a.lambda+W)+32*W)+
    GeneralPaperCatalogueSlotsPrice.width cap+GeneralPaperCatalogueSlotsPrice.profile model W cap+256*W

theorem bounded {n cap : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet) (response : Bool)
    (raw : FixedArrayTable n (Option Entry)) (hn : n≤cap)
    (hs : ∀ r e,raw.read r=some e → (GeneralPaperCodeDecode.decode a response e.cost).choice=some e.predecessor)
    (count : ℕ) (hc : count≤cap+1) : window model W a raw count hc≤profile model W cap a := by
  have hinput := GeneralPaperEncodedFixedVector.bounded_length W (GeneralPaperRawCatalogueStorage.entryCapacity W a.lambda) cap
    (GeneralPaperCodeRecordStorage.optionalEntry W) raw hn (by intro r; exact GeneralPaperCodeRecordStorage.optional_entry W a response _ (hs r))
  have hp := prefix_bound model W a response raw hs count hc
  have hf := frames_bound W n cap count hn hc
  have hz := GeneralPaperCodeRecordStorage.entry W a response (GeneralPaperCatalogueSlots.zero a) (GeneralPaperCodeDecodeSound.decode_zero a response)
  change GeneralPaperEncodedCatalogueStorage.entryBits W (GeneralPaperCatalogueSlots.zero a)≤entryCapacity W a.lambda at hz
  have hcurrent := current_bound (cap:=cap) model W a response raw hs count
  have hr := returned (cap:=cap) model W a response raw hs
  have hm := annotation_word cap
  change natBits (GeneralPaperCatalogueSlotsExecution.run (cap:=cap) true (fun w => w) model W a raw).1.2≤_ at hm
  have hsCost := GeneralPaperCatalogueSlotsPrice.bit_work (cap:=cap) model W a raw hn
  unfold window profile
  nlinarith only [hinput,hp,hf,hz,hcurrent,hr,hm,hsCost]

end Blotto.GeneralPaperCataloguePaddingStorage
