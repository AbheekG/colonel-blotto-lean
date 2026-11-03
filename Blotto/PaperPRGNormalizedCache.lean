import Blotto.PaperPRGInitializationFallbackCost

/-! The normalized sampler's budget, lengths and initial resources are
materialized once, with actual source arithmetic and array construction.
Its runtime system reads retained arrays. Original mathematical functions
occur only in correctness proofs; the draw needs no parameter-cost oracle.
-/

namespace Blotto.PaperPRGNormalizedCache
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem system_ext {n : ℕ} (first second : RationalLottoResourceSystem n)
    (hB : first.B=second.B) (hL : first.length=second.length) (hR : first.initial=second.initial) : first=second := by
  cases first
  cases second
  cases hB
  cases hL
  cases hR
  rfl

structure Cache {n : ℕ} (i : RationalLottoResourceSystem n) where
  budget : ℚ
  lengths : FixedArrayTable n ℚ
  resources : FixedArrayTable n ℚ
  budget_correct : budget=i.B
  lengths_correct : lengths.read=i.length
  resources_correct : resources.read=i.initial

def Cache.system {n : ℕ} {i : RationalLottoResourceSystem n} (p : Cache i) : RationalLottoResourceSystem n where
  B := p.budget
  length := p.lengths.read
  initial := p.resources.read
  B_pos := by rw [p.budget_correct]; exact i.B_pos
  length_pos := by rw [p.lengths_correct]; exact i.length_pos
  length_le := by rw [p.lengths_correct,p.budget_correct]; exact i.length_le
  initial_box := by rw [p.resources_correct,p.lengths_correct]; exact i.initial_box
  initial_sum := by rw [p.resources_correct,p.budget_correct]; exact i.initial_sum

theorem Cache.system_eq {n : ℕ} {i : RationalLottoResourceSystem n} (p : Cache i) : p.system=i := by
  exact system_ext p.system i p.budget_correct p.lengths_correct p.resources_correct

def source {n : ℕ} (i : RationalPRGOriginalInput n) (rich : Bool) : RationalLottoResourceSystem n :=
  if rich then i.normalizedInput.richNativeSystem else i.normalizedInput.poorNativeSystem

def build {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (W : ℕ) (rich : Bool) : Cache (source i rich) × ℕ :=
  let A := 4*W
  let ratio := i.b/i.a
  let lengths := PaperIndexedArrayConstruction.run primitive A
    (fun j => ((2:ℚ)*i.values j,RationalScaleRowCode.coordinateBitCost model 2 (i.values j)))
  let resources := if rich then (lengths.1,0) else
    PaperIndexedArrayConstruction.run primitive A
      (fun j => (ratio*lengths.1.read j,RationalScaleRowCode.coordinateBitCost model ratio (lengths.1.read j)))
  have hLengths : lengths.1.read=(source i rich).length := by
    rw [PaperIndexedArrayConstruction.run_data]
    funext j
    rw [FixedArrayTable.read_ofFn]
    cases rich <;> rfl
  have hResources : resources.1.read=(source i rich).initial := by
    dsimp only [resources]
    cases rich with
    | false =>
        simp only [Bool.false_eq_true,ite_false,PaperIndexedArrayConstruction.run_data]
        funext j
        rw [FixedArrayTable.read_ofFn,congrFun hLengths j]
        rfl
    | true => exact hLengths
  (⟨if rich then 1 else ratio,lengths.1,resources.1,
    by cases rich <;> rfl,hLengths,hResources⟩,
    i.normalizationBitWork model+lengths.2+resources.2+
      32*(A+primitive (binaryWordWidth (n+1))+1))

theorem build_budget {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (W : ℕ) (rich : Bool) :
    (build i model primitive W rich).1.budget = if rich then 1 else i.b/i.a := rfl

theorem build_lengths {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (W : ℕ) (rich : Bool) :
    (build i model primitive W rich).1.lengths.read=i.normalizedInput.lengths := by
  have h := (build i model primitive W rich).1.lengths_correct
  cases rich <;> exact h

theorem build_system {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (W : ℕ) (rich : Bool) :
    (build i model primitive W rich).1.system=source i rich := (build i model primitive W rich).1.system_eq

theorem build_work {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (W : ℕ) (rich : Bool) :
    (build i model primitive W rich).2 = i.normalizationBitWork model+
      RationalScaleRowCode.rowBitCost model 2 i.values+
      PaperIndexedArrayConstruction.overhead primitive (4*W) n n+
      (if rich then 0 else RationalScaleRowCode.rowBitCost model (i.b/i.a) i.normalizedInput.lengths+
        PaperIndexedArrayConstruction.overhead primitive (4*W) n n)+
      32*(4*W+primitive (binaryWordWidth (n+1))+1) := by
  unfold build
  dsimp only
  rw [PaperIndexedArrayConstruction.run_work]
  cases rich with
  | false =>
      simp only [Bool.false_eq_true,ite_false,PaperIndexedArrayConstruction.run_work,
        PaperIndexedArrayConstruction.run_data]
      have hRead : (FixedArrayTable.ofFn (fun j : Fin n => (2:ℚ)*i.values j)).read=i.normalizedInput.lengths := by
        funext j
        rw [FixedArrayTable.read_ofFn]
        rfl
      rw [hRead]
      unfold RationalScaleRowCode.rowBitCost
      omega
  | true => simp only [ite_true]; unfold RationalScaleRowCode.rowBitCost; omega

theorem value_height {n : ℕ} (i : RationalPRGOriginalInput n) (j : Fin n) :
    RationalHeight (i.values j) (3+i.originalInputWordWidth) := by
  have hSum : rationalWordWidth (i.values j) ≤ ∑ k,rationalWordWidth (i.values k) :=
    Finset.single_le_sum (fun k _ => Nat.zero_le (rationalWordWidth (i.values k))) (Finset.mem_univ j)
  exact (rationalHeight_of_wordWidth (i.values j)).mono (by
    unfold RationalPRGOriginalInput.originalInputWordWidth
    omega)

theorem arithmetic_bounds {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel) (K : ℕ) :
    i.normalizationBitWork model ≤ 5*model.rat (PRGPaperDrawCost.width i K) ∧
    RationalScaleRowCode.rowBitCost model 2 i.values ≤ 4*n*model.rat (PRGPaperDrawCost.width i K) ∧
    RationalScaleRowCode.rowBitCost model (i.b/i.a) i.normalizedInput.lengths ≤
      4*n*model.rat (PRGPaperDrawCost.width i K) := by
  let S := 3+i.originalInputWordWidth
  have hTwo : RationalHeight (2:ℚ) S := (show RationalHeight (2:ℚ) 3 by norm_num [RationalHeight]).mono (by dsimp [S]; omega)
  have hValue : ∀ j,RationalHeight (i.values j) S := value_height i
  have hLength : ∀ j,RationalHeight (i.normalizedInput.lengths j) (S+S) := by
    intro j
    exact hTwo.mul (hValue j)
  have hRatio : RationalHeight (i.b/i.a) S := i.normalized_budget_height
  have hWidth : 1+2*(S+(S+S)) ≤ PRGPaperDrawCost.width i K := by
    dsimp [S,PRGPaperDrawCost.width,RationalPRGLinearFramingWork.uniformWidth]
    omega
  have hSmall : 1+2*(S+S) ≤ PRGPaperDrawCost.width i K := by omega
  have hNormWidth : 1+2*i.originalInputWordWidth ≤ PRGPaperDrawCost.width i K := by dsimp [S] at hWidth; omega
  have hNorm := (i.normalizationBitWork_bound model).trans (Nat.mul_le_mul_left 5 (model.monotone hNormWidth))
  have hLengths := (RationalScaleRowCode.rowBitCost_bound model 2 i.values S S hTwo hValue).trans
    (Nat.mul_le_mul_left (4*n) (model.monotone hSmall))
  have hResources := (RationalScaleRowCode.rowBitCost_bound model (i.b/i.a) i.normalizedInput.lengths S (S+S)
    hRatio hLength).trans (Nat.mul_le_mul_left (4*n) (model.monotone hWidth))
  exact ⟨hNorm,hLengths,hResources⟩

theorem overhead_bound {n : ℕ} (i : RationalPRGOriginalInput n) (primitive : ℕ → ℕ)
    (c : ℕ) (hPrimitive : ∀ w,primitive w ≤ c*w) (K : ℕ) :
    PaperIndexedArrayConstruction.overhead primitive (4*PRGPaperDrawCost.width i K) n n ≤
      64*(c+1)*(n+1)*PRGPaperDrawCost.width i K := by
  let W := PRGPaperDrawCost.width i K
  have hf := PRGPaperDrawCost.width_facts i K
  have hIndex : binaryWordWidth (n+1) ≤ W :=
    ((binaryWordWidth_mono (show n+1 ≤ W+2 by have h := hf.2.1; omega)).trans (Nat.le_succ _)).trans
      (PRGPaperSharpDrawCost.logFactor_le_width i K)
  have hPay := Nat.mul_le_mul_left (10*c) hIndex
  have hPad := Nat.mul_le_mul_left 28 hf.1
  have hStep : 6*(4*W)+10*c*binaryWordWidth (n+1)+28 ≤ 64*(c+1)*W := by
    nlinarith only [hPay,hPad]
  have hTotal := Nat.mul_le_mul_left (n+1) hStep
  exact (PaperIndexedArrayConstruction.overhead_bound primitive c hPrimitive (4*W) n n le_rfl).trans
    (by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hTotal)

theorem build_work_bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w,primitive w ≤ c*w) (K : ℕ) (rich : Bool) :
    (build i model primitive (PRGPaperDrawCost.width i K) rich).2 ≤
      (8*n+5)*model.rat (PRGPaperDrawCost.width i K)+
        512*(c+1)*(n+1)*PRGPaperDrawCost.width i K := by
  let W := PRGPaperDrawCost.width i K
  have hArith := arithmetic_bounds i model K
  have hOverhead := overhead_bound i primitive c hPrimitive K
  have hf := PRGPaperDrawCost.width_facts i K
  have hIndex : binaryWordWidth (n+1) ≤ W :=
    ((binaryWordWidth_mono (show n+1 ≤ W+2 by have h := hf.2.1; omega)).trans (Nat.le_succ _)).trans
      (PRGPaperSharpDrawCost.logFactor_le_width i K)
  have hPay := (hPrimitive (binaryWordWidth (n+1))).trans (Nat.mul_le_mul_left c hIndex)
  have hPad : W ≤ (n+1)*W := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right W (show 1 ≤ n+1 by omega)
  have hWrapper : 32*(4*W+primitive (binaryWordWidth (n+1))+1) ≤ 192*(c+1)*W := by
    have hW : 1 ≤ W := hf.1
    nlinarith only [hPay,hW]
  have hWrapperN := Nat.mul_le_mul_left (192*(c+1)) hPad
  rw [build_work]
  cases rich <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;>
    change _ ≤ (8*n+5)*model.rat W+512*(c+1)*(n+1)*W <;>
    nlinarith only [hArith.1,hArith.2.1,hArith.2.2,hOverhead,hWrapper,hWrapperN]

end Blotto.PaperPRGNormalizedCache
