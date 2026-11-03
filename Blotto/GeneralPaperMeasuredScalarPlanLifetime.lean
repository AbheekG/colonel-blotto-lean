import Blotto.GeneralPaperMeasuredPlanLifetimeAlgebra

/-! Actual natural/rational payload measurers own their scan buffers,
scalar arithmetic scratch, returned plan and parent fields. Payload
precision contributes once through measured extent; saved prices use
encoded widths. The reference measurer has all three primitive windows. -/
namespace Blotto.GeneralPaperMeasuredScalarPlanLifetime
open GeneralPaperMeasuredBlockPlan
open GeneralPaperMeasuredPlanLifetimeAlgebra
open GeneralPaperEncodedScalarStorage
open GeneralPaperPayloadInstallationLifetime (cap)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def naturalWindow (model : RationalCostModel) (S : ℕ) (n : ℕ) : ℕ :=
  GeneralPaperWordLengthLifetime.footprint S n +
    GeneralPaperNaturalScalarLifetime.footprint model S .add (binaryWordWidth n) 1 +
    GeneralPaperMeasuredLayoutStorage.planFoot S (natural model S n) +
    fields S [S,(GeneralPaperStoredWordLength.run S n).1,(GeneralPaperStoredWordLength.run S n).2,
      (GeneralPaperNaturalScalarStep.run model S .add (binaryWordWidth n) 1).1,
      (GeneralPaperNaturalScalarStep.run model S .add (binaryWordWidth n) 1).2,(natural model S n).work] + 64 * S

theorem natural_good (model : RationalCostModel) (S A n : ℕ) (hA : 0 < A) :
    Good model S A 4 (natural model S n) (naturalWindow model S n) := by
  have hGood := GeneralPaperMeasuredLeafPlanWork.natural model S A n hA
  refine ⟨hGood.1,?_⟩
  intro Q hCap hWork
  have hScan := GeneralPaperWordLengthLifetime.bounded S n
  have hStep := GeneralPaperNaturalScalarLifetime.bounded model S .add (binaryWordWidth n) 1
  have hPrice := hGood.2 hCap
  have hPlan := plan_bound model S A Q (natural model S n) hGood.1 hA hCap hWork
  have hWhole := hWork
  change (GeneralPaperStoredWordLength.run S n).2 +
    (GeneralPaperNaturalScalarStep.run model S .add (binaryWordWidth n) 1).2 + 64 * S + 64 ≤ Q at hWork
  have hSize : (natural model S n).sizes.sum = natBits n := by rw [natural_data]; simp
  rw [hSize] at hCap hPrice hPlan ⊢
  have hLength := binaryWordWidth_le_of_lt_pow hA (show binaryWordWidth n < 2 ^ A by unfold natBits at hCap; omega)
  have hResult := binaryWordWidth_le_of_lt_pow hA hCap
  have hResultWord : natBits (natBits n) ≤ A + 1 := by change 1 + binaryWordWidth (natBits n) ≤ A + 1; omega
  have hSWord := Nat.add_le_add_left (binaryWordWidth_mono (show S ≤ cap S A Q by unfold cap; omega)) 1
  have hAWord := Nat.add_le_add_left (binaryWordWidth_mono (show A ≤ cap S A Q by unfold cap; omega)) 1
  change natBits S ≤ natBits (cap S A Q) at hSWord
  change natBits A ≤ natBits (cap S A Q) at hAWord
  have hFields := fields_bound S (A + 1 + natBits (cap S A Q))
    [S,(GeneralPaperStoredWordLength.run S n).1,(GeneralPaperStoredWordLength.run S n).2,
      (GeneralPaperNaturalScalarStep.run model S .add (binaryWordWidth n) 1).1,
      (GeneralPaperNaturalScalarStep.run model S .add (binaryWordWidth n) 1).2,(natural model S n).work] (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
    · omega
    · change natBits (binaryWordWidth n) ≤ _; unfold natBits; omega
    · have h := price_word S A Q (GeneralPaperStoredWordLength.run S n).2 (by omega); omega
    · simp only [GeneralPaperNaturalScalarStep.data,GeneralPaperNaturalScalarStep.Op.apply]
      have he : binaryWordWidth n + 1 = natBits n := by unfold natBits; omega
      rw [he]
      exact hResultWord.trans (by omega)
    · have h := price_word S A Q (GeneralPaperNaturalScalarStep.run model S .add (binaryWordWidth n) 1).2 (by omega); omega
    · have h := price_word S A Q (natural model S n).work hWhole; omega)
  change fields S _ ≤ 6 * (A + 1 + natBits (cap S A Q) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S A Q
  have hParent : fields S [S,(GeneralPaperStoredWordLength.run S n).1,(GeneralPaperStoredWordLength.run S n).2,
      (GeneralPaperNaturalScalarStep.run model S .add (binaryWordWidth n) 1).1,
      (GeneralPaperNaturalScalarStep.run model S .add (binaryWordWidth n) 1).2,(natural model S n).work] + 64 * S ≤ unit model S A Q := by omega
  have hScratch : GeneralPaperWordLengthLifetime.footprint S n +
      GeneralPaperNaturalScalarLifetime.footprint model S .add (binaryWordWidth n) 1 ≤
      32 * (natural model S n).work := by
    change _ + _ ≤ 32 * ((GeneralPaperStoredWordLength.run S n).2 +
      (GeneralPaperNaturalScalarStep.run model S .add (binaryWordWidth n) 1).2 + 64 * S + 64)
    omega
  have hPay := Nat.mul_le_mul_left (natBits n + 1)
    (show 32 * GeneralPaperMeasuredPlanWorkAlgebra.unit model S A ≤ unit model S A Q by omega)
  have hBase := Nat.mul_le_mul_right (unit model S A Q) (show 1 ≤ natBits n + 1 by omega)
  unfold naturalWindow
  nlinarith only [hScratch,hPrice,hPlan,hParent,hPay,hBase]

def rationalWindow (model : RationalCostModel) (S : ℕ) (q : ℚ) : ℕ :=
  GeneralPaperWordLengthLifetime.rationalFoot model S q +
    GeneralPaperMeasuredLayoutStorage.planFoot S (rational model S q) +
    fields S [S,(GeneralPaperStoredRationalWordLength.run model S q).1,
      (GeneralPaperStoredRationalWordLength.run model S q).2,(rational model S q).work] + 64 * S

theorem rational_good (model : RationalCostModel) (S A : ℕ) (q : ℚ) (hA : 0 < A) :
    Good model S A 4 (rational model S q) (rationalWindow model S q) := by
  have hGood := GeneralPaperMeasuredLeafPlanWork.rational model S A q hA
  refine ⟨hGood.1,?_⟩
  intro Q hCap hWork
  have hScratch := GeneralPaperWordLengthLifetime.rational_bounded model S q
  have hPrice := hGood.2 hCap
  have hPlan := plan_bound model S A Q (rational model S q) hGood.1 hA hCap hWork
  have hWhole := hWork
  change (GeneralPaperStoredRationalWordLength.run model S q).2 + 64 * S + 64 ≤ Q at hWork
  have hSize : (rational model S q).sizes.sum = rationalWordWidth q := by rw [rational_data]; simp
  rw [hSize] at hCap hPrice hPlan ⊢
  have hResult := binaryWordWidth_le_of_lt_pow hA hCap
  have hSWord := Nat.add_le_add_left (binaryWordWidth_mono (show S ≤ cap S A Q by unfold cap; omega)) 1
  have hAWord := Nat.add_le_add_left (binaryWordWidth_mono (show A ≤ cap S A Q by unfold cap; omega)) 1
  change natBits S ≤ natBits (cap S A Q) at hSWord
  change natBits A ≤ natBits (cap S A Q) at hAWord
  have hFields := fields_bound S (A + 1 + natBits (cap S A Q))
    [S,(GeneralPaperStoredRationalWordLength.run model S q).1,(GeneralPaperStoredRationalWordLength.run model S q).2,
      (rational model S q).work] (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl
    · omega
    · rw [GeneralPaperStoredRationalWordLength.data]; unfold natBits; omega
    · have h := price_word S A Q (GeneralPaperStoredRationalWordLength.run model S q).2 (by omega); omega
    · have h := price_word S A Q (rational model S q).work hWhole; omega)
  change fields S _ ≤ 4 * (A + 1 + natBits (cap S A Q) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S A Q
  have hParent : fields S [S,(GeneralPaperStoredRationalWordLength.run model S q).1,
      (GeneralPaperStoredRationalWordLength.run model S q).2,(rational model S q).work] + 64 * S ≤ unit model S A Q := by omega
  have hLocal : GeneralPaperWordLengthLifetime.rationalFoot model S q ≤
      rationalWordWidth q + 256 * (rational model S q).work := by
    change _ ≤ rationalWordWidth q + 256 * ((GeneralPaperStoredRationalWordLength.run model S q).2 + 64 * S + 64)
    omega
  have hPay := Nat.mul_le_mul_left (rationalWordWidth q + 1)
    (show 256 * GeneralPaperMeasuredPlanWorkAlgebra.unit model S A + 1 ≤ unit model S A Q by omega)
  have hBase := Nat.mul_le_mul_right (unit model S A Q) (show 1 ≤ rationalWordWidth q + 1 by omega)
  unfold rationalWindow
  nlinarith only [hLocal,hPrice,hPlan,hParent,hPay,hBase]

def referenceControls (model : RationalCostModel) (S A count stride fixed : ℕ) : List ℕ :=
  let p0 := (GeneralPaperNaturalScalarStep.run model S .mul stride count).2
  let p1 := (GeneralPaperNaturalScalarStep.run model S .add (stride * count) fixed).2
  let p2 := (GeneralPaperNaturalScalarStep.run model S .mul A (stride * count + fixed)).2
  [S,A,count,stride,fixed,p0,p1,p2,p0+p1,p0+p1+p2,(references model S A count stride fixed).work]

def referencesWindow (model : RationalCostModel) (S A count stride fixed : ℕ) : ℕ :=
  GeneralPaperNaturalScalarLifetime.footprint model S .mul stride count +
    GeneralPaperNaturalScalarLifetime.footprint model S .add (stride * count) fixed +
    GeneralPaperNaturalScalarLifetime.footprint model S .mul A (stride * count + fixed) +
    GeneralPaperMeasuredLayoutStorage.planFoot S (references model S A count stride fixed) +
    fields S (referenceControls model S A count stride fixed) + 192 * S

theorem references_good (model : RationalCostModel) (S A count stride fixed : ℕ) (hA : 0 < A)
    (hPos : 0 < A * (stride * count + fixed)) (hCount : binaryWordWidth count ≤ A + 8)
    (hStride : binaryWordWidth stride ≤ A + 8) (hFixed : binaryWordWidth fixed ≤ A + 8) :
    Good model S A 4 (references model S A count stride fixed) (referencesWindow model S A count stride fixed) := by
  have hPositive : GeneralPaperMeasuredPlanPositive.Positive (references model S A count stride fixed) := by
    rw [GeneralPaperMeasuredPlanPositive.Positive,references_data]
    intro x hx
    exact (List.mem_singleton.mp hx) ▸ hPos
  refine ⟨hPositive,?_⟩
  intro Q hCap hWork
  have hWhole := hWork
  change (GeneralPaperNaturalScalarStep.run model S .mul stride count).2 +
    (GeneralPaperNaturalScalarStep.run model S .add (stride * count) fixed).2 +
    (GeneralPaperNaturalScalarStep.run model S .mul A (stride * count + fixed)).2 + 64 * S + 64 ≤ Q at hWork
  have h0 := GeneralPaperNaturalScalarLifetime.bounded model S .mul stride count
  have h1 := GeneralPaperNaturalScalarLifetime.bounded model S .add (stride * count) fixed
  have h2 := GeneralPaperNaturalScalarLifetime.bounded model S .mul A (stride * count + fixed)
  have hPrice := GeneralPaperMeasuredLeafPlanWork.references_work model S A count stride fixed hCount hStride hFixed
  have hPlan := plan_bound model S A Q _ hPositive hA hCap hWhole
  have hSWord := Nat.add_le_add_left (binaryWordWidth_mono (show S ≤ cap S A Q by unfold cap; omega)) 1
  have hAWord := Nat.add_le_add_left (binaryWordWidth_mono (show A ≤ cap S A Q by unfold cap; omega)) 1
  change natBits S ≤ natBits (cap S A Q) at hSWord
  change natBits A ≤ natBits (cap S A Q) at hAWord
  have hFields := fields_bound S (A + 9 + natBits (cap S A Q)) (referenceControls model S A count stride fixed) (by
    intro x hx
    simp only [referenceControls,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|hx
    · omega
    · omega
    · unfold natBits; omega
    · unfold natBits; omega
    · unfold natBits; omega
    · have hp : x ≤ Q := by rcases hx with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
      have h := price_word S A Q x hp; omega)
  change fields S _ ≤ 11 * (A + 9 + natBits (cap S A Q) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S A Q
  have hParent : fields S (referenceControls model S A count stride fixed) + 192 * S ≤ unit model S A Q := by omega
  have hScratch : GeneralPaperNaturalScalarLifetime.footprint model S .mul stride count +
      GeneralPaperNaturalScalarLifetime.footprint model S .add (stride * count) fixed +
      GeneralPaperNaturalScalarLifetime.footprint model S .mul A (stride * count + fixed) ≤
      32 * (references model S A count stride fixed).work := by
    change _ ≤ 32 * ((GeneralPaperNaturalScalarStep.run model S .mul stride count).2 +
      (GeneralPaperNaturalScalarStep.run model S .add (stride * count) fixed).2 +
      (GeneralPaperNaturalScalarStep.run model S .mul A (stride * count + fixed)).2 + 64 * S + 64)
    omega
  have hPay : 32 * GeneralPaperMeasuredPlanWorkAlgebra.unit model S A ≤ unit model S A Q := by omega
  have hBase := Nat.mul_le_mul_right (unit model S A Q)
    (show 1 ≤ (references model S A count stride fixed).sizes.sum + 1 by omega)
  unfold referencesWindow
  nlinarith only [hScratch,hPrice,hPlan,hParent,hPay,hBase]

end Blotto.GeneralPaperMeasuredScalarPlanLifetime
