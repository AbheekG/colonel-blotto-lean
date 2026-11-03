import Blotto.PaperPRGConstructedDrawCost

/-! The exhaustion branch constructs the actual direct fallback with one
indexed pass. Rational word copies, the zero-index test, array construction
and sample-result wrappers have separate exact prices. This is source bit
work in the paper model, with no additional feasibility or native claim.
-/

namespace Blotto.PaperStoredFallbackConstruction
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

def indexWork {n : ℕ} (primitive : ℕ → ℕ) (j : Fin n) : ℕ :=
  binaryWordWidth (j.val+1)+primitive (binaryWordWidth (j.val+1))+6

def comparisonWork (primitive : ℕ → ℕ) (n : ℕ) : ℕ := ∑ j : Fin n,indexWork primitive j

def build {n : ℕ} (i : RationalLottoResourceSystem n) (primitive : ℕ → ℕ) (A : ℕ) :
    RationalResourceArray n × ℕ :=
  let returned := PaperIndexedArrayConstruction.run primitive A
    (fun j => (i.fallbackAllocation j,2*rationalWordWidth (i.fallbackAllocation j)+indexWork primitive j))
  (PaperStoredRowConstruction.resourceArray returned.1,returned.2)

theorem build_data {n : ℕ} (i : RationalLottoResourceSystem n) (primitive : ℕ → ℕ) (A : ℕ) :
    (build i primitive A).1 = RationalResourceArray.ofAllocation i.fallbackAllocation := by
  unfold build
  dsimp only
  rw [PaperIndexedArrayConstruction.run_data]
  rfl

theorem build_work {n : ℕ} (i : RationalLottoResourceSystem n) (primitive : ℕ → ℕ) (A : ℕ) :
    (build i primitive A).2 = i.fallbackRowBitCost+comparisonWork primitive n+
      PaperIndexedArrayConstruction.overhead primitive A n n := by
  unfold build
  dsimp only
  rw [PaperIndexedArrayConstruction.run_work]
  unfold RationalLottoResourceSystem.fallbackRowBitCost comparisonWork
  simp only [Finset.sum_add_distrib,Finset.mul_sum]

theorem comparisonWork_bound (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w,primitive w ≤ c*w) (n : ℕ) :
    comparisonWork primitive n ≤ n*((c+1)*binaryWordWidth (n+1)+6) := by
  have hEach (j : Fin n) : indexWork primitive j ≤ (c+1)*binaryWordWidth (n+1)+6 := by
    have hWidth := binaryWordWidth_mono (show j.val+1 ≤ n+1 by omega)
    have hPay := (hPrimitive (binaryWordWidth (j.val+1))).trans (Nat.mul_le_mul_left c hWidth)
    unfold indexWork
    nlinarith only [hWidth,hPay]
  calc
    _ ≤ ∑ _j : Fin n,((c+1)*binaryWordWidth (n+1)+6) := Finset.sum_le_sum (fun j _ => hEach j)
    _ = _ := by simp

def constructionExtra (primitive : ℕ → ℕ) (A n : ℕ) : ℕ :=
  comparisonWork primitive n+PaperIndexedArrayConstruction.overhead primitive A n n

def wrapperWork (primitive : ℕ → ℕ) (A R : ℕ) : ℕ :=
  6*A+4*primitive (binaryWordWidth (R+1))+20

def finish {n : ℕ} (i : RationalLottoResourceSystem n) (primitive : ℕ → ℕ)
    (A R : ℕ) (result : Option (RationalResourceArray n)) :
    RationalResourceArray n × ℕ :=
  match result with
  | none =>
      let fallback := build i primitive A
      (fallback.1,fallback.2+wrapperWork primitive A R)
  | some row => (row,wrapperWork primitive A R)

def fixedSample {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (W K R : ℕ) (outer scalar : Fin K → Bool) (choice : Fin R → Bool) :
    RationalResourceArray n × ℕ :=
  finish i primitive (StoredArrayReferenceList.poolAddressWidth n W) R
    (i.paperConstructedFixedRun model primitive W K R outer scalar choice).1

theorem fixedSample_data {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (W K R : ℕ) (outer scalar : Fin K → Bool) (choice : Fin R → Bool) :
    (fixedSample i model primitive W K R outer scalar choice).1 = i.storedFixedSample K R outer scalar choice := by
  unfold fixedSample finish
  rw [i.paperConstructedFixedRun_data]
  unfold RationalLottoResourceSystem.storedFixedSample
  cases h : (i.storedFixedRun K R outer scalar choice).1 <;> simp only [build_data]

def extra {n : ℕ} (i : RationalLottoResourceSystem n) (primitive : ℕ → ℕ)
    (W K R : ℕ) (outer scalar : Fin K → Bool) (choice : Fin R → Bool) : ℕ :=
  let A := StoredArrayReferenceList.poolAddressWidth n W
  (match (i.storedFixedRun K R outer scalar choice).1 with
    | none => constructionExtra primitive A n
    | some _ => 0)+wrapperWork primitive A R

theorem fixedSample_work {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (W K R : ℕ) (outer scalar : Fin K → Bool) (choice : Fin R → Bool) :
    (fixedSample i model primitive W K R outer scalar choice).2 =
      i.paperFallbackBitWork K R outer scalar choice+extra i primitive W K R outer scalar choice := by
  have hProjection := congrArg Prod.fst (i.storedFixedRun_projection K R outer scalar choice)
  change Option.map RationalResourceArray.allocation (i.storedFixedRun K R outer scalar choice).1 =
    (i.runShared K R outer scalar choice).1 at hProjection
  unfold fixedSample finish extra RationalLottoResourceSystem.paperFallbackBitWork
  rw [i.paperConstructedFixedRun_data,←hProjection]
  cases h : (i.storedFixedRun K R outer scalar choice).1 with
  | none => simp only [Option.map_none,build_work,constructionExtra]; omega
  | some row => simp only [Option.map_some,Nat.zero_add]

def sample {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (W K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    RationalResourceArray n × ℕ :=
  let inner := firstBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits
  fixedSample i model primitive W K (RationalLottoResourceSystem.coinBitBudget n K)
    (secondBitBlock (RationalLottoResourceSystem.innerBitBudget n K) K bits)
    (secondBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K inner)
    (firstBitBlock (RationalLottoResourceSystem.coinBitBudget n K) K inner)

theorem sample_data {n : ℕ} (i : RationalLottoResourceSystem n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (W K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    (sample i model primitive W K bits).1 = i.storedPaperSample K bits := by
  unfold sample RationalLottoResourceSystem.storedPaperSample
  exact fixedSample_data i model primitive W K _ _ _ _

theorem extra_bound {n : ℕ} (i : RationalLottoResourceSystem n) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w,primitive w ≤ c*w) (W K R : ℕ) (hn : n ≤ W) (hR : R ≤ W)
    (hW : 1 ≤ W) (hLog : binaryWordWidth (W+2)+1 ≤ W)
    (outer scalar : Fin K → Bool) (choice : Fin R → Bool) :
    extra i primitive W K R outer scalar choice ≤ 256*(c+1)*(n+1)*W := by
  have hIndex : binaryWordWidth (n+1) ≤ W :=
    ((binaryWordWidth_mono (by omega : n+1 ≤ W+2)).trans (Nat.le_succ _)).trans hLog
  have hReader : binaryWordWidth (R+1) ≤ W :=
    ((binaryWordWidth_mono (by omega : R+1 ≤ W+2)).trans (Nat.le_succ _)).trans hLog
  have hAddress := StoredArrayReferenceList.poolAddressWidth_log_bound n W
  have hWord : binaryWordWidth (W+1) ≤ W :=
    ((binaryWordWidth_mono (by omega : W+1 ≤ W+2)).trans (Nat.le_succ _)).trans hLog
  have hA : StoredArrayReferenceList.poolAddressWidth n W ≤ 2*W := by omega
  have hComparison := comparisonWork_bound primitive c hPrimitive n
  have hCompWord := Nat.mul_le_mul_left (n*(c+1)) hIndex
  have hOverhead := (PaperIndexedArrayConstruction.pool_overhead_bound primitive c hPrimitive n W hn).trans
    (Nat.mul_le_mul_left (64*(c+1)*(n+1)) hLog)
  have hReaderPay := (hPrimitive (binaryWordWidth (R+1))).trans (Nat.mul_le_mul_left c hReader)
  have hPad : W ≤ (n+1)*W := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right W (show 1 ≤ n+1 by omega)
  have hPadding := Nat.mul_le_mul_left (32*(c+1)) hPad
  have hLoops := Nat.mul_le_mul_left (n*6) hW
  unfold extra constructionExtra wrapperWork
  split <;> nlinarith only [hA,hComparison,hCompWord,hOverhead,hReaderPay,hPadding,hLoops,hW]

end Blotto.PaperStoredFallbackConstruction
