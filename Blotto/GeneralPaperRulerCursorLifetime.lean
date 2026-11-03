import Blotto.GeneralPaperBooleanRowCursorLifetime

/-! Actual ruler cursor: complete counted-list scan and pointer encoder,
original source list, returned directory, descriptor/read and saved prices.
The encoder's existing full lifetime is retained as a polylogarithmic factor. -/
namespace Blotto.GeneralPaperRulerCursorLifetime
open GeneralPaperSequentialLayout (Region)
open GeneralPaperEncodedScalarStorage
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit unit_bounds)
open GeneralPaperPayloadInstallationLifetime (cap)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def encoding (model : RationalCostModel) (S A : ℕ) : ℕ :=
  GeneralPaperWordEncodingLifetime.windowProfile model S A (A + 8)

def controls (model : RationalCostModel) (S A : ℕ) (source : List Unit) (header : Region A) (rest : List (Region A)) : List ℕ :=
  let bodyWork := (GeneralPaperMeasuredListBlockPlan.body model S (GeneralPaperEqualMeasuredLeafPlans.unit S) source).work
  let wordWork := (GeneralPaperStoredWordEncoding.word model S A source.length).2
  let readWork := GeneralPaperLastRegionSelection.price S A header
  [S,A,source.length,bodyWork,wordWork,bodyWork + wordWork,readWork,bodyWork + wordWork + readWork,
    (GeneralPaperRulerFieldCursor.run model S A source (header :: rest)).work]

def window (model : RationalCostModel) (S A start : ℕ) (source : List Unit) (rest : List (Region A)) : ℕ :=
  let header := GeneralPaperScalarRecordComponents.listHeader A start 32 2 source.length
  GeneralPaperMeasuredListPlanLifetime.bodyWindow model S A (GeneralPaperEqualMeasuredLeafPlans.unit S)
      (fun x => GeneralPaperMeasuredRecordPlanLifetime.constantWindow S (GeneralPaperEqualMeasuredLeafPlans.unit S x)) source +
    GeneralPaperWordEncodingLifetime.window model S A source.length +
    listFootprint S (fun _ : Unit => 1) source +
    GeneralPaperFieldDirectoryStorage.directoryFoot S (GeneralPaperRulerFieldCursor.expected A start source) +
    GeneralPaperMeasuredLayoutStorage.regionFoot S header + GeneralPaperLastRegionSelection.price S A header +
    fields S (controls model S A source header rest) + 128 * S

theorem window_bound (model : RationalCostModel) (S A start Q : ℕ) (source : List Unit) (rest : List (Region A))
    (hA : 0 < A)
    (hCap : start + (GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (GeneralPaperEqualMeasuredLeafPlans.unit S) source).sizes.sum < 2 ^ A)
    (hWork : (GeneralPaperRulerFieldCursor.run model S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start
        (GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (GeneralPaperEqualMeasuredLeafPlans.unit S) source)).1 ++ rest)).work ≤ Q) :
    window model S A start source rest ≤
      ((GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (GeneralPaperEqualMeasuredLeafPlans.unit S) source).sizes.sum + 1) *
        (32 + encoding model S A) * unit model S A Q := by
  let header := GeneralPaperScalarRecordComponents.listHeader A start 32 2 source.length
  have hStream : (GeneralPaperMeasuredBlockLayout.run model S A start
      (GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (GeneralPaperEqualMeasuredLeafPlans.unit S) source)).1 = [header] := by
    simp only [GeneralPaperMeasuredBlockLayout.run,GeneralPaperRulerFieldCursor.plan,GeneralPaperSequentialLayout.run,
      GeneralPaperStoredWordEncoding.word_data,header,GeneralPaperScalarRecordComponents.listHeader]
  rw [hStream,List.singleton_append] at hWork
  have hWhole := hWork
  have hTotal : (GeneralPaperRulerFieldCursor.run model S A source (header :: rest)).work =
      (GeneralPaperMeasuredListBlockPlan.body model S (GeneralPaperEqualMeasuredLeafPlans.unit S) source).work +
      (GeneralPaperStoredWordEncoding.word model S A source.length).2 +
      GeneralPaperLastRegionSelection.price S A header + 128 * (S + A + 1) := by
    simp only [GeneralPaperRulerFieldCursor.run,GeneralPaperMeasuredListBlockPlan.body_count]
  rw [hTotal] at hWork
  have hCount := GeneralPaperRulerFieldCursor.count_fits model S A start source hA hCap
  have hWidth := binaryWordWidth_le_of_lt_pow hA hCount
  have hZero : (source.map (fun x => (GeneralPaperEqualMeasuredLeafPlans.unit S x).sizes.sum)).sum = 0 := by
    simp [GeneralPaperEqualMeasuredLeafPlans.unit,GeneralPaperEqualMeasuredLeafPlans.empty]
  have hBody := GeneralPaperMeasuredListPlanLifetime.body_bound model S A 2 Q
    (GeneralPaperEqualMeasuredLeafPlans.unit S)
    (fun x => GeneralPaperMeasuredRecordPlanLifetime.constantWindow S (GeneralPaperEqualMeasuredLeafPlans.unit S x))
    source hA (fun _ _ => GeneralPaperMeasuredRecordPlanLifetime.empty_good model S A hA)
    (by omega) (by rw [hZero]; positivity) (by omega)
  rw [hZero] at hBody
  have hEncoding := GeneralPaperWordEncodingLifetime.word_bound model S A source.length (A + 8) (by omega)
  have hPositive := GeneralPaperMeasuredPlanPositive.list model S A 2 32 (GeneralPaperEqualMeasuredLeafPlans.unit S) source hA (by omega)
    (fun _ _ => GeneralPaperEqualMeasuredPlanPositive.empty S)
  have hDirectory := GeneralPaperFieldDirectoryStorage.directory_bound model S A start
    (GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (GeneralPaperEqualMeasuredLeafPlans.unit S) source)
    (GeneralPaperRulerFieldCursor.expected A start source)
    (GeneralPaperRulerFieldCursor.success model S A start source rest).2.2.1 hPositive hA hCap
  have hRawCap : start + A * (2 * source.length + 32) < 2 ^ A := by
    simpa only [GeneralPaperRulerFieldCursor.plan,List.sum_cons,List.sum_nil,Nat.add_zero] using hCap
  have hRegion := GeneralPaperMeasuredLayoutStorage.region_bound S A header hA hRawCap
  have hRead := GeneralPaperDirectoryCopyWork.region_work model S A header hA hRawCap
  have hWord : ∀ z ≤ cap S A Q,natBits z ≤ A + 9 + natBits (cap S A Q) := by
    intro z hz
    have h := Nat.add_le_add_left (binaryWordWidth_mono hz) 1
    change natBits z ≤ natBits (cap S A Q) at h
    omega
  have hCountWord : natBits source.length ≤ A + 9 + natBits (cap S A Q) := by unfold natBits; omega
  have hFields := fields_bound S (A + 9 + natBits (cap S A Q)) (controls model S A source header rest) (by
    intro x hx
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact hCountWord | (apply hWord; unfold cap; omega))
  change fields S _ ≤ 9 * (A + 9 + natBits (cap S A Q) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S A Q
  have hUnitPos : 0 < unit model S A Q := by omega
  have hN : source.length ≤ A * (2 * source.length + 32) := by
    have h := Nat.mul_le_mul_right (2 * source.length + 32) hA
    nlinarith only [h]
  have hSource := list_bound S 1 (fun _ : Unit => 1) source (fun _ _ => le_rfl)
  have hLinks := Nat.mul_le_mul_left source.length (show 1 + 2 * S ≤ unit model S A Q by omega)
  have hBodyMass := Nat.mul_le_mul_right (14 * unit model S A Q) (Nat.add_le_add_right hN 1)
  have hSourceMass := Nat.mul_le_mul_right (unit model S A Q) hN
  have hDirectoryPay := Nat.mul_le_mul_left (A * (2 * source.length + 32) + 1)
    (show 2048 * (S + A + 1) ≤ unit model S A Q by omega)
  have hParent : GeneralPaperMeasuredLayoutStorage.regionFoot S header + GeneralPaperLastRegionSelection.price S A header +
      fields S (controls model S A source header rest) + 160 * S ≤ unit model S A Q := by
    unfold GeneralPaperMeasuredLayoutStorage.regionBound at hRegion
    omega
  have hEncPay : encoding model S A ≤ encoding model S A * unit model S A Q := Nat.le_mul_of_pos_right _ hUnitPos
  have hEncMass := Nat.mul_le_mul_right (encoding model S A * unit model S A Q)
    (show 1 ≤ A * (2 * source.length + 32) + 1 by omega)
  have hBase := Nat.mul_le_mul_right (unit model S A Q)
    (show 1 ≤ A * (2 * source.length + 32) + 1 by omega)
  rw [GeneralPaperRulerFieldCursor.plan,List.sum_cons,List.sum_nil,Nat.add_zero] at hDirectory ⊢
  dsimp only [GeneralPaperFieldDirectoryStorage.bound] at hDirectory
  change GeneralPaperWordEncodingLifetime.window model S A source.length ≤ encoding model S A at hEncoding
  simp only [Nat.zero_add] at hBody
  unfold window
  nlinarith only [hBody,hBodyMass,hEncoding,hEncPay,hEncMass,hSource,hLinks,hSourceMass,hDirectory,hDirectoryPay,hParent,hBase]

end Blotto.GeneralPaperRulerCursorLifetime
