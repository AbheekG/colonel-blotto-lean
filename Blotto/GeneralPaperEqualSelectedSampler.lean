import Blotto.GeneralPaperEqualBitCanonical

/-! A measured local draw closure for either selected return. The grouped
case reuses its stored reference; the pure case measures its sole budget and
constructs a local reference. One extra address bit covers the outer closure.
Draws use only this retained closure and random inputs. -/
namespace Blotto.GeneralPaperEqualSelectedSampler
open GeneralPaperEqualBitBranch (Prepared)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

def baseReference {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} : Prepared v k budget → ℕ
  | .dominant _ _ _ _ => GeneralPaperEqualBitDrawRates.address n 0 k (rationalWordWidth budget)
  | .grouped _ sampler _ _ => sampler.address

structure Sampler {n : ℕ} (v : RationalFieldSelector n) (k : ℕ) (budget : ℚ) where
  branch : Prepared v k budget
  address : ℕ
  address_correct : address = baseReference branch + 1

def measuredBase {n : ℕ} (model : RationalCostModel) (A k : ℕ) (budget : ℚ)
    {v : RationalFieldSelector n} : Prepared v k budget → ℕ × ℕ
  | .dominant _ _ _ _ =>
    let word := GeneralPaperStoredRationalWordLength.run model A budget
    let address := GeneralPaperEqualAddressConstruction.run model A n 0 k word.1
    (address.1, word.2 + address.2)
  | .grouped _ sampler _ _ => (sampler.address, 32 * A + 32)

theorem measured_base_data {n : ℕ} (model : RationalCostModel) (A k : ℕ) (budget : ℚ)
    {v : RationalFieldSelector n} (p : Prepared v k budget) :
    (measuredBase model A k budget p).1 = baseReference p := by
  cases p with
  | dominant chosen heavy row correct =>
    simp only [measuredBase, baseReference, GeneralPaperEqualAddressConstruction.data,
      GeneralPaperStoredRationalWordLength.data]
  | grouped small sampler hK hB => rfl

def close {n : ℕ} (model : RationalCostModel) (A k : ℕ) (budget : ℚ)
    {v : RationalFieldSelector n} (p : Prepared v k budget) : Sampler v k budget × ℕ :=
  let base := measuredBase model A k budget p
  let actual : Sampler v k budget := ⟨p, base.1 + 1, congrArg (fun a => a + 1) (measured_base_data model A k budget p)⟩
  (actual, base.2 + GeneralPaperEqualAddressConstruction.price model A base.1 1 actual.address + 64 * A + 64)

theorem close_branch {n : ℕ} (model : RationalCostModel) (A k : ℕ) (budget : ℚ)
    {v : RationalFieldSelector n} (p : Prepared v k budget) : (close model A k budget p).1.branch = p := rfl

theorem close_address {n : ℕ} (model : RationalCostModel) (A k : ℕ) (budget : ℚ)
    {v : RationalFieldSelector n} (p : Prepared v k budget) :
    (close model A k budget p).1.address = baseReference p + 1 :=
  (close model A k budget p).1.address_correct

noncomputable def traceLaw {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (a : Sampler v k budget) :=
  GeneralPaperEqualBitBranchDraw.traceLaw a.branch

noncomputable def observed {n : ℕ} (model : RationalCostModel) {v : RationalFieldSelector n}
    {k : ℕ} {budget : ℚ} (a : Sampler v k budget) := GeneralPaperEqualBitBranchDraw.observed model a.address a.branch

noncomputable def realDecode {n : ℕ} (model : RationalCostModel) {v : RationalFieldSelector n}
    {k : ℕ} {budget : ℚ} (a : Sampler v k budget) := GeneralPaperEqualBitBranchDraw.realDecode model a.address a.branch

noncomputable def outputLaw {n : ℕ} (model : RationalCostModel) {v : RationalFieldSelector n}
    {k : ℕ} {budget : ℚ} (a : Sampler v k budget) := GeneralPaperEqualBitBranch.outputLaw model a.branch

theorem base_bound {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (p : Prepared v k budget) :
    baseReference p ≤ 2 * GeneralPaperEqualBitDrawRates.log n k (rationalWordWidth budget) := by
  cases p with
  | dominant chosen heavy row correct => exact (GeneralPaperEqualBitDrawRates.metadata_bounds n 0 k _ (by omega)).1
  | grouped small sampler hK hB =>
    have h := (GeneralPaperEqualBitDrawRates.metadata_bounds n _ sampler.exponent
      (rationalWordWidth sampler.prepared.budget) (GeneralPaperEqualNativeCache.group_count v small)).1
    rw [← sampler.address_correct, hK, hB] at h
    exact h

theorem address_bound {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (a : Sampler v k budget) :
    a.address ≤ 2 * GeneralPaperEqualBitDrawRates.log n k (rationalWordWidth budget) + 1 := by
  rw [a.address_correct]
  exact Nat.add_le_add_right (base_bound a.branch) 1

theorem law {n : ℕ} (model : RationalCostModel) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) : (traceLaw a).map (realDecode model a) = outputLaw model a :=
  GeneralPaperEqualBitBranchDraw.law model a.address a.branch

theorem completed_ae {n : ℕ} (model : RationalCostModel) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) :
    ∀ᵐ trace ∂(traceLaw a : MeasureTheory.Measure (GeneralPaperEqualBitBranchDraw.Trace a.branch)),
      ∃ row, (observed model a trace).output = some row :=
  GeneralPaperEqualBitBranchDraw.completed_ae model a.address a.branch

theorem completed_budget {n : ℕ} (model : RationalCostModel) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) (hB : 0 ≤ budget) (trace : GeneralPaperEqualBitBranchDraw.Trace a.branch)
    (row : RationalResourceArray n) (h : (observed model a trace).output = some row) :
    FullBudget (budget : ℝ) row.realAllocation :=
  GeneralPaperEqualBitBranchDraw.completed_budget model a.address a.branch hB trace row h

end Blotto.GeneralPaperEqualSelectedSampler
