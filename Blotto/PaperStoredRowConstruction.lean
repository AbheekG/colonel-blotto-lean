import Blotto.PaperIndexedArrayConstruction

/-! The actual stored output scaling is implemented by the priced indexed
constructor. The callback is the existing exact rational multiplication and
its existing operand-sensitive source ledger. Every coordinate, array field
and index/control word is charged, independently of the native implementation.
-/

namespace Blotto.PaperStoredRowConstruction
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

def resourceArray {n : ℕ} (table : FixedArrayTable n ℚ) : RationalResourceArray n :=
  ⟨table.data,table.size⟩

def scale {n : ℕ} (model : RationalCostModel) (primitive : ℕ → ℕ) (addressWidth : ℕ)
    (a : ℚ) (row : RationalResourceArray n) : RationalResourceArray n × ℕ :=
  let returned := PaperIndexedArrayConstruction.run primitive addressWidth
    (fun j => (a*row.allocation j,RationalScaleRowCode.coordinateBitCost model a (row.allocation j)))
  (resourceArray returned.1,returned.2)

theorem scale_data {n : ℕ} (model : RationalCostModel) (primitive : ℕ → ℕ) (addressWidth : ℕ)
    (a : ℚ) (row : RationalResourceArray n) :
    (scale model primitive addressWidth a row).1 = row.scaled a := by
  unfold scale
  dsimp only
  rw [PaperIndexedArrayConstruction.run_data]
  unfold resourceArray FixedArrayTable.ofFn RationalResourceArray.scaled
  congr 1
  apply Array.ext
  · simp only [Array.size_ofFn,Array.size_map,row.size]
  · intro j hj hk
    simp only [Array.getElem_ofFn,Array.getElem_map,RationalResourceArray.allocation]

theorem scale_work {n : ℕ} (model : RationalCostModel) (primitive : ℕ → ℕ) (addressWidth : ℕ)
    (a : ℚ) (row : RationalResourceArray n) :
    (scale model primitive addressWidth a row).2 =
      RationalScaleRowCode.rowBitCost model a row.allocation+
        PaperIndexedArrayConstruction.overhead primitive addressWidth n n := by
  exact PaperIndexedArrayConstruction.run_work primitive addressWidth
    (fun j => (a*row.allocation j,RationalScaleRowCode.coordinateBitCost model a (row.allocation j)))

def originalRow {n : ℕ} (i : RationalPRGOriginalInput n) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : RationalResourceArray n :=
  if rich then i.normalizedInput.richNativeSystem.storedPaperSample K bits
  else i.normalizedInput.poorNativeSystem.storedPaperSample K bits

def originalScale {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : RationalResourceArray n × ℕ :=
  scale model primitive (StoredArrayReferenceList.poolAddressWidth n (PRGPaperDrawCost.width i K))
    i.a (originalRow i rich K bits)

theorem originalScale_data {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    (originalScale i model primitive rich K bits).1 =
      NativePRGPreparedSampler.sample (NativePRGPreparedSampler.ofInput i K) rich bits := by
  rw [originalScale,scale_data]
  cases rich <;> rfl

theorem originalScale_work {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    (originalScale i model primitive rich K bits).2 =
      (if rich then i.richScalingBitWork model K bits else i.poorScalingBitWork model K bits)+
        PaperIndexedArrayConstruction.overhead primitive
          (StoredArrayReferenceList.poolAddressWidth n (PRGPaperDrawCost.width i K)) n n := by
  rw [originalScale,scale_work]
  cases rich with
  | false =>
      simp only [originalRow,Bool.false_eq_true,ite_false,
        RationalLottoResourceSystem.storedPaperSample_allocation]
      rfl
  | true =>
      simp only [originalRow,ite_true,RationalLottoResourceSystem.storedPaperSample_allocation]
      rfl

theorem originalScale_work_bound {n : ℕ} (i : RationalPRGOriginalInput n) (model : RationalCostModel)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w,primitive w ≤ c*w) (rich : Bool) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    (originalScale i model primitive rich K bits).2 ≤
      4*n*model.rat (PRGPaperDrawCost.width i K)+64*(c+1)*(n+1)*PRGPaperDrawCost.width i K := by
  have hf := PRGPaperDrawCost.width_facts i K
  have hn : n ≤ PRGPaperDrawCost.width i K := (show n ≤ n+K+1 by omega).trans hf.2.1
  have hOverhead := (PaperIndexedArrayConstruction.pool_overhead_bound primitive c hPrimitive
    n (PRGPaperDrawCost.width i K) hn).trans
      (Nat.mul_le_mul_left (64*(c+1)*(n+1)) (PRGPaperSharpDrawCost.logFactor_le_width i K))
  have hWidths := RationalPRGLinearFramingWork.width_bounds i K
  have hScaling : i.scalingWidth K ≤ PRGPaperDrawCost.width i K := hWidths.2.2.2.2.1
  have hPrice := Nat.mul_le_mul_left (4*n) (model.monotone hScaling)
  have hScale := i.scalingBitWork_bounds model K bits
  rw [originalScale_work]
  cases rich <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

end Blotto.PaperStoredRowConstruction
