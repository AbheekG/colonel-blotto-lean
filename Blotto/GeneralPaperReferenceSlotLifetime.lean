import Blotto.GeneralPaperSelectedCountPreparationLifetime

/-! A complete temporary reference entry owns its natural position as well
as location/target words. Slot construction includes all five arithmetic
operand/result/scratch reserves, address encoding and saved partial prices.
The entry position is caller data even though RAM installation projects it
away. No size or storage observer executes in the constructor. -/
namespace Blotto.GeneralPaperReferenceSlotLifetime
open GeneralPaperEncodedScalarStorage
open GeneralPaperReferenceSlotConstruction (Entry run)
open GeneralPaperStoredReferenceReadWork (envelope slotBound slot_widths)
open GeneralPaperReferenceRegionSlots
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def entryFoot {A : ℕ} (S : ℕ) (entry : Entry A) : ℕ := natBits entry.position + 2 * A + 64 * S

def prices (model : RationalCostModel) (S A base fixed stride index cell : ℕ) (target : FixedBinaryWord A) : List ℕ :=
  let p0 := (GeneralPaperNaturalScalarStep.run model S .mul stride index).2
  let p1 := (GeneralPaperNaturalScalarStep.run model S .add fixed (stride * index)).2
  let p2 := (GeneralPaperNaturalScalarStep.run model S .add (fixed + stride * index) cell).2
  let p3 := (GeneralPaperNaturalScalarStep.run model S .mul A (fixed + stride * index + cell)).2
  let p4 := (GeneralPaperNaturalScalarStep.run model S .add base (A * (fixed + stride * index + cell))).2
  let p5 := (GeneralPaperStoredWordEncoding.word model S A (base + A * (fixed + stride * index + cell))).2
  [p0,p0+p1,p0+p1+p2,p0+p1+p2+p3,p0+p1+p2+p3+p4,p0+p1+p2+p3+p4+p5,
    (run model S A base fixed stride index cell target).2]

def controls (model : RationalCostModel) (S A base fixed stride index cell : ℕ) (target : FixedBinaryWord A) : List ℕ :=
  [S,A,base,fixed,stride,index,cell] ++ prices model S A base fixed stride index cell target

def wordLimit (model : RationalCostModel) (S A L : ℕ) : ℕ :=
  envelope L + natBits (slotBound model S A L) + natBits S + 1

theorem prices_bounded (model : RationalCostModel) (S A base fixed stride index cell Q : ℕ)
    (target : FixedBinaryWord A) (hWork : (run model S A base fixed stride index cell target).2 ≤ Q) :
    ∀ price ∈ prices model S A base fixed stride index cell target,price ≤ Q := by
  have hWhole := hWork
  dsimp only [run] at hWork
  simp only [GeneralPaperNaturalScalarStep.data,GeneralPaperNaturalScalarStep.Op.apply] at hWork
  intro price hp
  simp only [prices,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

theorem control_words (model : RationalCostModel) (S A base fixed stride index cell L : ℕ)
    (target : FixedBinaryWord A) (hA : binaryWordWidth A ≤ L) (hBase : binaryWordWidth base ≤ L)
    (hFixed : binaryWordWidth fixed ≤ L) (hStride : binaryWordWidth stride ≤ L)
    (hIndex : binaryWordWidth index ≤ L) (hCell : binaryWordWidth cell ≤ L) :
    ∀ x ∈ controls model S A base fixed stride index cell target,natBits x ≤ wordLimit model S A L := by
  obtain ⟨bA,bBase,bFixed,bStride,bIndex,bCell,_,_,_,_,_⟩ :=
    slot_widths A base fixed stride index cell L hA hBase hFixed hStride hIndex hCell
  have hWork := GeneralPaperStoredReferenceReadWork.slot_work model S A base fixed stride index cell L target
    hA hBase hFixed hStride hIndex hCell
  intro x hx
  simp only [controls,List.mem_append] at hx
  rcases hx with hx | hx
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    change natBits A ≤ envelope L at bA
    change natBits base ≤ envelope L at bBase
    change natBits fixed ≤ envelope L at bFixed
    change natBits stride ≤ envelope L at bStride
    change natBits index ≤ envelope L at bIndex
    change natBits cell ≤ envelope L at bCell
    unfold wordLimit
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  · have hp := prices_bounded model S A base fixed stride index cell _ target hWork x hx
    have hb := Nat.add_le_add_left (binaryWordWidth_mono hp) 1
    change natBits x ≤ natBits (slotBound model S A L) at hb
    unfold wordLimit
    omega

def window (model : RationalCostModel) (S A base fixed stride index cell : ℕ) (target : FixedBinaryWord A) : ℕ :=
  GeneralPaperNaturalScalarLifetime.footprint model S .mul stride index +
    GeneralPaperNaturalScalarLifetime.footprint model S .add fixed (stride * index) +
    GeneralPaperNaturalScalarLifetime.footprint model S .add (fixed + stride * index) cell +
    GeneralPaperNaturalScalarLifetime.footprint model S .mul A (fixed + stride * index + cell) +
    GeneralPaperNaturalScalarLifetime.footprint model S .add base (A * (fixed + stride * index + cell)) +
    GeneralPaperWordEncodingLifetime.window model S A (base + A * (fixed + stride * index + cell)) +
    entryFoot S (run model S A base fixed stride index cell target).1 +
    fields S (controls model S A base fixed stride index cell target) + 256 * S

def profile (model : RationalCostModel) (S A L : ℕ) : ℕ :=
  160 * (5 * model.rat (envelope L) + 16 * S + 16) +
    GeneralPaperWordEncodingLifetime.windowProfile model S A (envelope L) + envelope L + 2 * A + 64 * S +
    14 * (wordLimit model S A L + S) + 288 * S

theorem window_bound (model : RationalCostModel) (S A base fixed stride index cell L : ℕ)
    (target : FixedBinaryWord A) (hA : binaryWordWidth A ≤ L) (hBase : binaryWordWidth base ≤ L)
    (hFixed : binaryWordWidth fixed ≤ L) (hStride : binaryWordWidth stride ≤ L)
    (hIndex : binaryWordWidth index ≤ L) (hCell : binaryWordWidth cell ≤ L) :
    window model S A base fixed stride index cell target ≤ profile model S A L := by
  obtain ⟨bA,bBase,bFixed,bStride,bIndex,bCell,b0,b1,b2,b3,b4⟩ :=
    slot_widths A base fixed stride index cell L hA hBase hFixed hStride hIndex hCell
  have p0 := (GeneralPaperNaturalScalarLifetime.bounded model S .mul stride index).trans
    (Nat.mul_le_mul_left 32 (GeneralPaperNaturalScalarStep.work model S .mul stride index (envelope L) bStride bIndex b0))
  have p1 := (GeneralPaperNaturalScalarLifetime.bounded model S .add fixed (stride * index)).trans
    (Nat.mul_le_mul_left 32 (GeneralPaperNaturalScalarStep.work model S .add fixed (stride * index) (envelope L) bFixed b0 b1))
  have p2 := (GeneralPaperNaturalScalarLifetime.bounded model S .add (fixed + stride * index) cell).trans
    (Nat.mul_le_mul_left 32 (GeneralPaperNaturalScalarStep.work model S .add (fixed + stride * index) cell (envelope L) b1 bCell b2))
  have p3 := (GeneralPaperNaturalScalarLifetime.bounded model S .mul A (fixed + stride * index + cell)).trans
    (Nat.mul_le_mul_left 32 (GeneralPaperNaturalScalarStep.work model S .mul A (fixed + stride * index + cell) (envelope L) bA b2 b3))
  have p4 := (GeneralPaperNaturalScalarLifetime.bounded model S .add base (A * (fixed + stride * index + cell))).trans
    (Nat.mul_le_mul_left 32 (GeneralPaperNaturalScalarStep.work model S .add base (A * (fixed + stride * index + cell)) (envelope L) bBase b3 b4))
  have hEncoding := GeneralPaperWordEncodingLifetime.word_bound model S A (base + A * (fixed + stride * index + cell)) (envelope L)
    (by change 1 + binaryWordWidth (base + A * (fixed + stride * index + cell)) ≤ envelope L at b4; omega)
  have hEntry : entryFoot S (run model S A base fixed stride index cell target).1 ≤ envelope L + 2 * A + 64 * S := by
    unfold entryFoot
    rw [GeneralPaperReferenceSlotConstruction.position]
    change natBits (base + A * (fixed + stride * index + cell)) ≤ envelope L at b4
    omega
  have hFields := fields_bound S (wordLimit model S A L) (controls model S A base fixed stride index cell target)
    (control_words model S A base fixed stride index cell L target hA hBase hFixed hStride hIndex hCell)
  change fields S _ ≤ 14 * (wordLimit model S A L + S) + 32 * S at hFields
  unfold window profile
  omega

theorem header_entry_bound (model : RationalCostModel) (S A : ℕ) (header : Header A)
    (hA : 0 < A) (hValid : Valid header) (hCap : header.region.stop < 2 ^ A)
    (entry : Entry A) (he : entry ∈ (batch model S A header).entries) :
    entryFoot S entry ≤ 3 * A + 64 * S + 1 := by
  obtain ⟨i,target,_,hi,rfl⟩ := GeneralPaperReferenceSlotBatch.member_index model S A header.region.start header.fixed 1 0 0 header.targets entry he
  have hFits := GeneralPaperReferenceSlotConstruction.fits model S A header.region.start header.fixed 1 header.targets.length i 0 target
    (by omega) (by decide) (capacity header hValid hCap)
  have hWidth := binaryWordWidth_le_of_lt_pow hA hFits
  unfold entryFoot natBits
  omega

theorem header_slot_bound (model : RationalCostModel) (S A : ℕ) (header : Header A)
    (hA : 0 < A) (hValid : Valid header) (hCap : header.region.stop < 2 ^ A)
    (index : ℕ) (hIndex : index < header.targets.length) (target : FixedBinaryWord A) :
    window model S A header.region.start header.fixed 1 index 0 target ≤ profile model S A (A + 8) := by
  obtain ⟨hBase,_,hFixed,hCount⟩ := GeneralPaperStoredHeaderPreparationWork.owner_widths header hA hValid hCap
  exact window_bound model S A _ _ _ _ _ _ target
    (by have h := Nat.log2_le_self A; unfold binaryWordWidth; omega)
    (by omega) (by omega) (by change 1 ≤ A + 8; omega)
    ((binaryWordWidth_mono (Nat.le_of_lt hIndex)).trans (by omega)) (by change 1 ≤ A + 8; omega)

end Blotto.GeneralPaperReferenceSlotLifetime
