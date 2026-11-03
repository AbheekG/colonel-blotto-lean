import Blotto.GeneralPaperReferenceSlotLifetime

/-! Complete actual header batch construction. Each entry includes its
position scalar, and every activation reserves slot-construction/increment
scratch, cursor fields and saved prices. Only one output entry list is owned;
reached recursive outputs share its exact suffix. -/
namespace Blotto.GeneralPaperReferenceBatchLifetime
open GeneralPaperEncodedScalarStorage
open GeneralPaperReferenceSlotConstruction (Entry)
open GeneralPaperReferenceRegionSlots
open GeneralPaperReferenceSlotBatch (run)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def wordLimit (S A Q : ℕ) : ℕ := A + 9 + natBits Q + natBits S + 1

def prices (model : RationalCostModel) (S A base fixed start : ℕ) (value : FixedBinaryWord A)
    (values : List (FixedBinaryWord A)) : List ℕ :=
  let p := (GeneralPaperReferenceSlotConstruction.run model S A base fixed 1 start 0 value).2
  let increment := (GeneralPaperNaturalScalarStep.run model S .add start 1).2
  [p,increment,(run model S A base fixed 1 0 (start + 1) values).work,
    (run model S A base fixed 1 0 start (value :: values)).work,p + increment]

def controls (model : RationalCostModel) (S A base fixed start : ℕ) (value : FixedBinaryWord A)
    (values : List (FixedBinaryWord A)) : List ℕ :=
  [S,A,base,fixed,start,(GeneralPaperNaturalScalarStep.run model S .add start 1).1,
    (run model S A base fixed 1 0 (start + 1) values).next] ++ prices model S A base fixed start value values

theorem prices_bounded (model : RationalCostModel) (S A base fixed start Q : ℕ) (value : FixedBinaryWord A)
    (values : List (FixedBinaryWord A)) (hWork : (run model S A base fixed 1 0 start (value :: values)).work ≤ Q) :
    ∀ p ∈ prices model S A base fixed start value values,p ≤ Q := by
  have hWhole := hWork
  change (GeneralPaperReferenceSlotConstruction.run model S A base fixed 1 start 0 value).2 +
    (GeneralPaperNaturalScalarStep.run model S .add start 1).2 + (run model S A base fixed 1 0 (start + 1) values).work +
    128 * (S + A + 1) ≤ Q at hWork
  intro p hp
  simp only [prices,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl <;> omega

theorem control_words (model : RationalCostModel) (S A base fixed start Q : ℕ) (value : FixedBinaryWord A)
    (values : List (FixedBinaryWord A)) (hBase : binaryWordWidth base ≤ A + 8)
    (hFixed : binaryWordWidth fixed ≤ A + 8) (hCount : binaryWordWidth (start + (value :: values).length) ≤ A + 8)
    (hWork : (run model S A base fixed 1 0 start (value :: values)).work ≤ Q) :
    ∀ x ∈ controls model S A base fixed start value values,natBits x ≤ wordLimit S A Q := by
  have hAWord := GeneralPaperNaturalScalarLifetime.counter_word A
  have hStart := binaryWordWidth_mono (show start ≤ start + (value :: values).length by omega)
  have hNext := binaryWordWidth_mono (show start + 1 ≤ start + (value :: values).length by simp only [List.length_cons]; omega)
  have hLater : (run model S A base fixed 1 0 (start + 1) values).next = start + (value :: values).length := by
    rw [GeneralPaperReferenceSlotBatch.next]
    simp only [List.length_cons]
    omega
  intro x hx
  simp only [controls,List.mem_append] at hx
  rcases hx with hx | hx
  · simp only [GeneralPaperNaturalScalarStep.data,GeneralPaperNaturalScalarStep.Op.apply,hLater,
      List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold wordLimit natBits at *
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  · have h := Nat.add_le_add_left (binaryWordWidth_mono
      (prices_bounded model S A base fixed start Q value values hWork x hx)) 1
    change natBits x ≤ natBits Q at h
    unfold wordLimit
    omega

def localFoot (model : RationalCostModel) (S A base fixed start : ℕ) (value : FixedBinaryWord A)
    (values : List (FixedBinaryWord A)) : ℕ :=
  GeneralPaperReferenceSlotLifetime.window model S A base fixed 1 start 0 value +
    GeneralPaperNaturalScalarLifetime.footprint model S .add start 1 +
    fields S (controls model S A base fixed start value values) + 192 * S

def frameUnit (model : RationalCostModel) (S A Q : ℕ) : ℕ :=
  GeneralPaperReferenceSlotLifetime.profile model S A (A + 8) +
    32 * GeneralPaperStoredHeaderPreparationWork.scalarBound model S A + 12 * (wordLimit S A Q + S) + 224 * S

theorem local_bound (model : RationalCostModel) (S A base fixed start Q : ℕ) (value : FixedBinaryWord A)
    (values : List (FixedBinaryWord A)) (hBase : binaryWordWidth base ≤ A + 8)
    (hFixed : binaryWordWidth fixed ≤ A + 8) (hCount : binaryWordWidth (start + (value :: values).length) ≤ A + 8)
    (hWork : (run model S A base fixed 1 0 start (value :: values)).work ≤ Q) :
    localFoot model S A base fixed start value values ≤ frameUnit model S A Q := by
  have hIndex := (binaryWordWidth_mono (show start ≤ start + (value :: values).length by omega)).trans hCount
  have hSlot := GeneralPaperReferenceSlotLifetime.window_bound model S A base fixed 1 start 0 (A + 8) value
    (by have h := Nat.log2_le_self A; unfold binaryWordWidth; omega) hBase hFixed
    (by change 1 ≤ A + 8; omega) hIndex (by change 1 ≤ A + 8; omega)
  have hIncrement := (GeneralPaperNaturalScalarLifetime.bounded model S .add start 1).trans
    (Nat.mul_le_mul_left 32 (GeneralPaperStoredHeaderPreparationWork.increment_work model S A start hIndex))
  have hFields := fields_bound S (wordLimit S A Q) (controls model S A base fixed start value values)
    (control_words model S A base fixed start Q value values hBase hFixed hCount hWork)
  change fields S _ ≤ 12 * (wordLimit S A Q + S) + 32 * S at hFields
  unfold localFoot frameUnit
  omega

def frames (model : RationalCostModel) (S A base fixed : ℕ) : ℕ → List (FixedBinaryWord A) → ℕ
  | start,[] => fields S [S,A,base,fixed,start,(run model S A base fixed 1 0 start []).work] + 64 * S
  | start,value :: values => localFoot model S A base fixed start value values + frames model S A base fixed (start + 1) values

theorem frames_bound (model : RationalCostModel) (S A base fixed start Q : ℕ) (values : List (FixedBinaryWord A))
    (hBase : binaryWordWidth base ≤ A + 8) (hFixed : binaryWordWidth fixed ≤ A + 8)
    (hCount : binaryWordWidth (start + values.length) ≤ A + 8)
    (hWork : (run model S A base fixed 1 0 start values).work ≤ Q) :
    frames model S A base fixed start values ≤ (values.length + 1) * frameUnit model S A Q := by
  induction values generalizing start with
  | nil =>
    have hAWord := GeneralPaperNaturalScalarLifetime.counter_word A
    simp only [List.length_nil,Nat.add_zero] at hCount
    have hFields := fields_bound S (wordLimit S A Q) [S,A,base,fixed,start,(run model S A base fixed 1 0 start []).work] (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      have hPrice := Nat.add_le_add_left (binaryWordWidth_mono hWork) 1
      change natBits (run model S A base fixed 1 0 start []).work ≤ natBits Q at hPrice
      unfold wordLimit natBits at *
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
    change fields S _ ≤ 6 * (wordLimit S A Q + S) + 32 * S at hFields
    simp only [frames,List.length_nil,Nat.zero_add,Nat.one_mul]
    unfold frameUnit
    omega
  | cons value values ih =>
    have hWhole := hWork
    have hTailWork : (run model S A base fixed 1 0 (start + 1) values).work ≤ Q := by
      change (GeneralPaperReferenceSlotConstruction.run model S A base fixed 1 start 0 value).2 +
        (GeneralPaperNaturalScalarStep.run model S .add start 1).2 + (run model S A base fixed 1 0 (start + 1) values).work +
        128 * (S + A + 1) ≤ Q at hWork
      omega
    have hEnd : start + 1 + values.length = start + (value :: values).length := by simp only [List.length_cons]; omega
    have hTail := ih (start + 1) (by rw [hEnd]; exact hCount) hTailWork
    have hLocal := local_bound model S A base fixed start Q value values hBase hFixed hCount hWhole
    simp only [frames,List.length_cons]
    nlinarith only [hTail,hLocal]

def window (model : RationalCostModel) (S A : ℕ) (header : Header A) : ℕ :=
  frames model S A header.region.start header.fixed 0 header.targets +
    listFootprint S (GeneralPaperReferenceSlotLifetime.entryFoot S) (batch model S A header).entries +
    fields S [(batch model S A header).next,(batch model S A header).work] + 64 * S

def unit (model : RationalCostModel) (S A Q : ℕ) : ℕ :=
  frameUnit model S A Q + 3 * A + 1 + 66 * S + 2 * (wordLimit S A Q + S) + 128 * S

theorem window_bound (model : RationalCostModel) (S A Q : ℕ) (header : Header A)
    (hA : 0 < A) (hValid : Valid header) (hCap : header.region.stop < 2 ^ A)
    (hWork : (batch model S A header).work ≤ Q) :
    window model S A header ≤ (header.targets.length + 1) * unit model S A Q := by
  obtain ⟨hBase,_,hFixed,hCount⟩ := GeneralPaperStoredHeaderPreparationWork.owner_widths header hA hValid hCap
  have hFrames := frames_bound model S A header.region.start header.fixed 0 Q header.targets (by omega) (by omega)
    (by simpa only [Nat.zero_add] using hCount.trans (show A ≤ A + 8 by omega)) hWork
  have hList := list_bound S (3 * A + 64 * S + 1) (GeneralPaperReferenceSlotLifetime.entryFoot S)
    (batch model S A header).entries (GeneralPaperReferenceSlotLifetime.header_entry_bound model S A header hA hValid hCap)
  have hLength : (batch model S A header).entries.length = header.targets.length :=
    GeneralPaperReferenceSlotBatch.count model S A header.region.start header.fixed 1 0 0 header.targets
  rw [hLength] at hList
  have hFields := fields_bound S (wordLimit S A Q) [(batch model S A header).next,(batch model S A header).work] (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    have hNext : (batch model S A header).next = header.targets.length := by
      exact (GeneralPaperReferenceSlotBatch.next model S A header.region.start header.fixed 1 0 0 header.targets).trans (by omega)
    have hPrice := Nat.add_le_add_left (binaryWordWidth_mono hWork) 1
    change natBits (batch model S A header).work ≤ natBits Q at hPrice
    unfold wordLimit natBits at *
    rcases hx with rfl|rfl
    · rw [hNext]; omega
    · omega)
  change fields S _ ≤ 2 * (wordLimit S A Q + S) + 32 * S at hFields
  have hReserve := GeneralPaperHeaderCountExpansionLifetime.reserve
    (2 * (wordLimit S A Q + S) + 128 * S) header.targets.length
  unfold window unit
  nlinarith only [hFrames,hList,hFields,hReserve]

end Blotto.GeneralPaperReferenceBatchLifetime
