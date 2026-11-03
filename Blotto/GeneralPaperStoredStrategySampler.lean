import Blotto.GeneralPaperSamplingControls

/-! A closed finite sampler retains original maps, budget, description and
all row/shift controls. Drawing reads these fields and fresh bits only; no
precision, power, source, row table or circle preparation executes again. -/
namespace Blotto.GeneralPaperStoredStrategySampler
open GeneralPaperStrategyDescription GeneralPaperSamplingControls
set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 16384

def castDescription {n T U K : ℕ} (o : GeneralPaperReducedValuesDriver.Output n) (h : T=U) (description : Description o T K) :
    Description o U K := h ▸ description

structure Sampler (n T K : ℕ) where
  original : GeneralPaperReducedValuesDriver.Output n
  budget : ℚ
  controls : Controls T
  description : Description original T K

def store {n T K : ℕ} (primitive : ℕ → ℕ) (A k : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) (hm : 0<o.m)
    (budget : ℚ) (description : Description o T K) (hDyadic : ∃ R,T=2^R) : Sampler n T K×ℕ :=
  let controls := GeneralPaperSamplingControls.make primitive A k o hm description hDyadic
  (⟨o,budget,controls.1,description⟩,controls.2+64*A)

theorem store_data {n T K : ℕ} (primitive : ℕ → ℕ) (A k : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) (hm : 0<o.m)
    (budget : ℚ) (description : Description o T K) (hDyadic : ∃ R,T=2^R) (R : ℕ) (hT : T=2^R) :
    (store primitive A k o hm budget description hDyadic).1=
      ⟨o,budget,specification T R k hT,description⟩ := by
  dsimp only [store]
  rw [GeneralPaperSamplingControls.data primitive A k o hm description hDyadic R hT]

def run {n T K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A : ℕ) (model : RationalCostModel) (sampler : Sampler n T K)
    (reciprocal : Bool) (fresh : Fin (sampler.controls.rowBits+sampler.controls.shiftBits) → Bool) : GeneralPaperNativeFairSampler.Result n :=
  let native := castDescription sampler.original sampler.controls.rows_eq.symm sampler.description
  let chosen := GeneralPaperStrategyDescription.run bits primitive A sampler.controls.rowBits sampler.controls.shiftBits sampler.controls.shifts
    sampler.controls.rows_power sampler.controls.shifts_power model sampler.original native
    (if reciprocal then sampler.budget else 1) reciprocal fresh
  {chosen with work := chosen.work+64*A}

noncomputable def law {n T K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A : ℕ) (model : RationalCostModel) (sampler : Sampler n T K)
    (reciprocal : Bool) : Mixed n :=
  (fairBitLaw (sampler.controls.rowBits+sampler.controls.shiftBits)).map
    (fun fresh j => ((run bits primitive A model sampler reciprocal fresh).output.read j:ℝ))

theorem law_data {n T K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A : ℕ) (model : RationalCostModel)
    (o : GeneralPaperReducedValuesDriver.Output n) (budget : ℚ) (R k : ℕ) (hT : T=2^R) (description : Description o T K) (reciprocal : Bool) :
    law bits primitive A model (⟨o,budget,specification T R k hT,description⟩:Sampler n T K) reciprocal=
      GeneralPaperStrategyDescription.law bits primitive A R (k+6) (GeneralPaperNativeSelectedSecurity.count k) hT
        (GeneralPaperNativeSelectedSecurity.count_power k) model o description (if reciprocal then budget else 1) reciprocal := rfl

theorem fresh_reads {n T K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A : ℕ) (model : RationalCostModel) (sampler : Sampler n T K)
    (reciprocal : Bool) (fresh : Fin (sampler.controls.rowBits+sampler.controls.shiftBits) → Bool) :
    (run bits primitive A model sampler reciprocal fresh).freshReads=sampler.controls.rowBits+sampler.controls.shiftBits :=
  GeneralPaperStrategyDescription.fresh_reads bits primitive A _ _ _ sampler.controls.rows_power sampler.controls.shifts_power
    model sampler.original (castDescription sampler.original sampler.controls.rows_eq.symm sampler.description)
    (if reciprocal then sampler.budget else 1) reciprocal fresh

theorem buffer_reads {n T K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A : ℕ) (model : RationalCostModel) (sampler : Sampler n T K)
    (reciprocal : Bool) (fresh : Fin (sampler.controls.rowBits+sampler.controls.shiftBits) → Bool) :
    (run bits primitive A model sampler reciprocal fresh).bufferReads=sampler.controls.rowBits+sampler.controls.shiftBits :=
  GeneralPaperStrategyDescription.buffer_reads bits primitive A _ _ _ sampler.controls.rows_power sampler.controls.shifts_power
    model sampler.original (castDescription sampler.original sampler.controls.rows_eq.symm sampler.description)
    (if reciprocal then sampler.budget else 1) reciprocal fresh

theorem logarithmic_bits {n T K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A : ℕ) (model : RationalCostModel) (sampler : Sampler n T K)
    (reciprocal : Bool) (fresh : Fin (sampler.controls.rowBits+sampler.controls.shiftBits) → Bool) :
    (run bits primitive A model sampler reciprocal fresh).freshReads=Nat.log2 (sampler.controls.rows*sampler.controls.shifts) := by
  rw [fresh_reads,sampler.controls.rows_power,sampler.controls.shifts_power,←pow_add,Nat.log2_two_pow]

theorem independent_players {n T K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A : ℕ) (model : RationalCostModel) (sampler : Sampler n T K) :
    let D := sampler.controls.rowBits+sampler.controls.shiftBits
    MeasureTheory.Measure.map (fun fresh =>
      ((fun j => ((run bits primitive A model sampler false (firstBitBlock D D fresh)).output.read j:ℝ)),
        (fun j => ((run bits primitive A model sampler true (secondBitBlock D D fresh)).output.read j:ℝ))))
      (fairBitLaw (D+D) : MeasureTheory.Measure (Fin (D+D) → Bool))=
      (law bits primitive A model sampler false : MeasureTheory.Measure (Allocation n)).prod
        (law bits primitive A model sampler true : MeasureTheory.Measure (Allocation n)) :=
  fairBitBlocks_map_product _ _
    (fun fresh j => ((run bits primitive A model sampler false fresh).output.read j:ℝ))
    (fun fresh j => ((run bits primitive A model sampler true fresh).output.read j:ℝ))

theorem every_output_feasible {n T K : ℕ} (bits : Bool) (primitive : ℕ → ℕ) (A : ℕ) (model : RationalCostModel) (sampler : Sampler n T K)
    (reciprocal : Bool) (B : ℝ) (h : Supported B (law bits primitive A model sampler reciprocal))
    (fresh : Fin (sampler.controls.rowBits+sampler.controls.shiftBits) → Bool) :
    Feasible B (fun j => ((run bits primitive A model sampler reciprocal fresh).output.read j:ℝ)) :=
  GeneralPaperStrategyDescription.every_output_feasible bits primitive A _ _ _ sampler.controls.rows_power sampler.controls.shifts_power model
    sampler.original (castDescription sampler.original sampler.controls.rows_eq.symm sampler.description)
    (if reciprocal then sampler.budget else 1) reciprocal B h fresh

theorem store_work {n T K : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (A k : ℕ)
    (o : GeneralPaperReducedValuesDriver.Output n) (hm : 0<o.m) (budget : ℚ) (description : Description o T K) (hDyadic : ∃ R,T=2^R) :
    (store primitive A k o hm budget description hDyadic).2≤profile primitive A T k+64*A :=
  Nat.add_le_add_right (GeneralPaperSamplingControls.work primitive hMono A k o hm description hDyadic) _

end Blotto.GeneralPaperStoredStrategySampler
