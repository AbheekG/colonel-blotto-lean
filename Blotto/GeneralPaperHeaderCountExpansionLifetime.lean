import Blotto.GeneralPaperHeaderWordLoopsLifetime

/-! Complete actual count-header expansion: original/returned header owners,
target-count copying, count/zero encoding scratch, padding/append activations
and every saved partial price. The zero-prefix branch keeps its actual path.
Each bound retains the header's local reserved-prefix-plus-target mass. -/
namespace Blotto.GeneralPaperHeaderCountExpansionLifetime
open GeneralPaperEncodedScalarStorage
open GeneralPaperReferenceRegionSlots
open GeneralPaperHeaderTargetCopyLifetime (cap)
open GeneralPaperHeaderCountExpansion (run)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem reserve (C M : ℕ) : C ≤ (M + 1) * C := by
  simpa only [Nat.one_mul] using Nat.mul_le_mul_right C (show 1 ≤ M + 1 by omega)

def commonWindow (model : RationalCostModel) (S A : ℕ) (header : Header A) : ℕ :=
  GeneralPaperFieldDirectoryStorage.headerFoot S header +
    GeneralPaperFieldDirectoryStorage.headerFoot S (run model S A header).1 +
    GeneralPaperMeasuredLayoutStorage.regionFoot S header.region +
    fields S [S,A,header.fixed,(run model S A header).2] + 192 * S

def commonUnit (S A B Q : ℕ) : ℕ :=
  768 * (S + A + 1) + GeneralPaperMeasuredLayoutStorage.regionBound S A +
    4 * (natBits (cap S A B Q) + S) + 224 * S

theorem common_bound (model : RationalCostModel) (S A B Q : ℕ) (header : Header A)
    (hA : 0 < A) (hValid : Valid header) (hCap : header.region.stop < 2 ^ A)
    (hMass : header.fixed + header.targets.length ≤ B) (hWork : (run model S A header).2 ≤ Q) :
    commonWindow model S A header ≤ (header.fixed + header.targets.length + 1) * commonUnit S A B Q := by
  have hSource := GeneralPaperFieldDirectoryStorage.header_bound S A header hA hValid hCap
  have hTarget := GeneralPaperFieldDirectoryStorage.header_bound S A (GeneralPaperHeaderCountExpansion.expanded header) hA
    (GeneralPaperHeaderCountExpansion.valid header hValid) (by rw [GeneralPaperHeaderCountExpansion.region]; exact hCap)
  rw [GeneralPaperStoredHeaderPreparationWork.expanded_length] at hTarget
  have hReturned : GeneralPaperFieldDirectoryStorage.headerFoot S (run model S A header).1 ≤
      (header.fixed + header.targets.length + 1) * 384 * (S + A + 1) := by
    simpa only [GeneralPaperHeaderCountExpansion.data] using hTarget
  have hHeaderFactor := Nat.mul_le_mul_right (384 * (S + A + 1))
    (show header.targets.length + 1 ≤ header.fixed + header.targets.length + 1 by omega)
  have hRegion := GeneralPaperMeasuredLayoutStorage.region_bound S A header.region hA hCap
  have hRegionFactor := reserve (GeneralPaperMeasuredLayoutStorage.regionBound S A) (header.fixed + header.targets.length)
  have hFields := fields_bound S (natBits (cap S A B Q)) [S,A,header.fixed,(run model S A header).2] (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 4 * (natBits (cap S A B Q) + S) + 32 * S at hFields
  have hFieldsFactor := reserve (4 * (natBits (cap S A B Q) + S) + 224 * S) (header.fixed + header.targets.length)
  unfold commonWindow commonUnit
  nlinarith only [hSource,hReturned,hHeaderFactor,hRegion,hRegionFactor,hFields,hFieldsFactor]

def positiveControls (model : RationalCostModel) (S A : ℕ) (header : Header A) : List ℕ :=
  let copied := GeneralPaperHeaderTargetCopy.run model S A header.targets
  let count := GeneralPaperStoredWordEncoding.word model S A copied.count
  let zero := GeneralPaperStoredWordEncoding.word model S A 0
  let padding := GeneralPaperHeaderTargetCopy.padding S A zero.1 (header.fixed - 1)
  let combined := GeneralPaperHeaderTargetCopy.append S A (count.1 :: padding.1) copied.values
  let region := GeneralPaperLastRegionSelection.price S A header.region
  let priceTotal := copied.work + count.2 + zero.2 + padding.2 + combined.2
  [S,A,copied.count,copied.work,count.2,zero.2,padding.2,combined.2,region,header.fixed - 1,
    copied.work + count.2,copied.work + count.2 + zero.2,copied.work + count.2 + zero.2 + padding.2,
    priceTotal,priceTotal + region,priceTotal + region + natBits header.fixed]

theorem component_prices (model : RationalCostModel) (S A Q : ℕ) (header : Header A)
    (hf : header.fixed ≠ 0) (hWork : (run model S A header).2 ≤ Q) :
    let copied := GeneralPaperHeaderTargetCopy.run model S A header.targets
    let count := GeneralPaperStoredWordEncoding.word model S A copied.count
    let zero := GeneralPaperStoredWordEncoding.word model S A 0
    let padding := GeneralPaperHeaderTargetCopy.padding S A zero.1 (header.fixed - 1)
    copied.work ≤ Q ∧ count.2 ≤ Q ∧ zero.2 ≤ Q ∧ padding.2 ≤ Q ∧
      (GeneralPaperHeaderTargetCopy.append S A (count.1 :: padding.1) copied.values).2 ≤ Q := by
  simp only [run,hf,ite_false] at hWork
  dsimp only
  omega

theorem positive_controls_bounded (model : RationalCostModel) (S A B Q : ℕ) (header : Header A)
    (hf : header.fixed ≠ 0) (hMass : header.fixed + header.targets.length ≤ B)
    (hWork : (run model S A header).2 ≤ Q) :
    ∀ x ∈ positiveControls model S A header,x ≤ cap S A B Q := by
  have hCount := GeneralPaperHeaderTargetCopy.count model S A header.targets
  simp only [run,hf,ite_false] at hWork
  intro x hx
  simp only [positiveControls,List.mem_cons,List.not_mem_nil,or_false] at hx
  unfold cap
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

def positiveWindow (model : RationalCostModel) (S A : ℕ) (header : Header A) : ℕ :=
  let copied := GeneralPaperHeaderTargetCopy.run model S A header.targets
  let count := GeneralPaperStoredWordEncoding.word model S A copied.count
  let zero := GeneralPaperStoredWordEncoding.word model S A 0
  let padding := GeneralPaperHeaderTargetCopy.padding S A zero.1 (header.fixed - 1)
  GeneralPaperHeaderTargetCopyLifetime.window model S A header.targets +
    GeneralPaperWordEncodingLifetime.window model S A copied.count + GeneralPaperWordEncodingLifetime.window model S A 0 +
    GeneralPaperHeaderWordLoopsLifetime.paddingWindow S A (header.fixed - 1) zero.1 +
    GeneralPaperHeaderWordLoopsLifetime.appendFrames S A (count.1 :: padding.1) copied.values +
    fields S (positiveControls model S A header) + 192 * S

def positiveUnit (model : RationalCostModel) (S A B Q : ℕ) : ℕ :=
  GeneralPaperHeaderTargetCopyLifetime.unit model S A B Q +
    2 * GeneralPaperWordEncodingLifetime.windowProfile model S A (A + 8) +
    GeneralPaperHeaderWordLoopsLifetime.paddingUnit S A B Q + GeneralPaperHeaderWordLoopsLifetime.appendUnit S A Q +
    16 * (natBits (cap S A B Q) + S) + 224 * S

theorem positive_bound (model : RationalCostModel) (S A B Q : ℕ) (header : Header A)
    (hA : 0 < A) (hValid : Valid header) (hCap : header.region.stop < 2 ^ A)
    (hf : header.fixed ≠ 0) (hMass : header.fixed + header.targets.length ≤ B) (hWork : (run model S A header).2 ≤ Q) :
    positiveWindow model S A header ≤ (header.fixed + header.targets.length + 1) * positiveUnit model S A B Q := by
  obtain ⟨_,_,_,hWidth⟩ := GeneralPaperStoredHeaderPreparationWork.owner_widths header hA hValid hCap
  have hPrices := component_prices model S A Q header hf hWork
  have hCopy := GeneralPaperHeaderTargetCopyLifetime.window_bound model S A B Q header.targets (by omega) (by omega) hPrices.1
  have hCopyFactor := Nat.mul_le_mul_right (GeneralPaperHeaderTargetCopyLifetime.unit model S A B Q)
    (show header.targets.length + 1 ≤ header.fixed + header.targets.length + 1 by omega)
  have hEncoded := GeneralPaperWordEncodingLifetime.word_bound model S A
    (GeneralPaperHeaderTargetCopy.run model S A header.targets).count (A + 8) (by rw [GeneralPaperHeaderTargetCopy.count]; omega)
  have hZero := GeneralPaperWordEncodingLifetime.word_bound model S A 0 (A + 8) (by change 1 ≤ A + 8; omega)
  have hEncodeFactor := reserve (2 * GeneralPaperWordEncodingLifetime.windowProfile model S A (A + 8)) (header.fixed + header.targets.length)
  have hPadding := GeneralPaperHeaderWordLoopsLifetime.padding_window_bound S A B Q (header.fixed - 1)
    (GeneralPaperStoredWordEncoding.word model S A 0).1 (by omega) hPrices.2.2.2.1
  have hPaddingFactor := Nat.mul_le_mul_right (GeneralPaperHeaderWordLoopsLifetime.paddingUnit S A B Q)
    (show header.fixed - 1 + 1 ≤ header.fixed + header.targets.length + 1 by omega)
  have hAppend := GeneralPaperHeaderWordLoopsLifetime.append_frames_bound S A Q
    ((GeneralPaperStoredWordEncoding.word model S A (GeneralPaperHeaderTargetCopy.run model S A header.targets).count).1 ::
      (GeneralPaperHeaderTargetCopy.padding S A (GeneralPaperStoredWordEncoding.word model S A 0).1 (header.fixed - 1)).1)
    (GeneralPaperHeaderTargetCopy.run model S A header.targets).values hPrices.2.2.2.2
  have hAppendLength :
      ((GeneralPaperStoredWordEncoding.word model S A (GeneralPaperHeaderTargetCopy.run model S A header.targets).count).1 ::
        (GeneralPaperHeaderTargetCopy.padding S A (GeneralPaperStoredWordEncoding.word model S A 0).1 (header.fixed - 1)).1).length = header.fixed := by
    rw [List.length_cons,GeneralPaperHeaderTargetCopy.padding_data,List.length_replicate]
    omega
  rw [hAppendLength] at hAppend
  have hAppendFactor := Nat.mul_le_mul_right (GeneralPaperHeaderWordLoopsLifetime.appendUnit S A Q)
    (show header.fixed + 1 ≤ header.fixed + header.targets.length + 1 by omega)
  have hFields := fields_bound S (natBits (cap S A B Q)) (positiveControls model S A header) (by
    intro x hx
    exact Nat.add_le_add_left (binaryWordWidth_mono (positive_controls_bounded model S A B Q header hf hMass hWork x hx)) 1)
  change fields S _ ≤ 16 * (natBits (cap S A B Q) + S) + 32 * S at hFields
  have hFieldsFactor := reserve (16 * (natBits (cap S A B Q) + S) + 224 * S) (header.fixed + header.targets.length)
  dsimp only [positiveWindow,positiveUnit]
  nlinarith only [hCopy,hCopyFactor,hEncoded,hZero,hEncodeFactor,hPadding,hPaddingFactor,hAppend,hAppendFactor,hFields,hFieldsFactor]

def window (model : RationalCostModel) (S A : ℕ) (header : Header A) : ℕ :=
  commonWindow model S A header + if header.fixed = 0 then 0 else positiveWindow model S A header

def unit (model : RationalCostModel) (S A B Q : ℕ) : ℕ := commonUnit S A B Q + positiveUnit model S A B Q

theorem window_bound (model : RationalCostModel) (S A B Q : ℕ) (header : Header A)
    (hA : 0 < A) (hValid : Valid header) (hCap : header.region.stop < 2 ^ A)
    (hMass : header.fixed + header.targets.length ≤ B) (hWork : (run model S A header).2 ≤ Q) :
    window model S A header ≤ (header.fixed + header.targets.length + 1) * unit model S A B Q := by
  have hCommon := common_bound model S A B Q header hA hValid hCap hMass hWork
  by_cases hf : header.fixed = 0
  · simp only [window,hf,ite_true,Nat.add_zero]
    unfold unit
    nlinarith only [hCommon,hf,Nat.zero_le ((header.fixed + header.targets.length + 1) * positiveUnit model S A B Q)]
  · have hPositive := positive_bound model S A B Q header hA hValid hCap hf hMass hWork
    simp only [window,hf,ite_false]
    unfold unit
    nlinarith only [hCommon,hPositive]

end Blotto.GeneralPaperHeaderCountExpansionLifetime
