import Blotto.GeneralPaperDirectRowExactSampler

/-! Final row/shift interface on the actually retained unequal sampler.
Direct descriptions use one shift and zero shift bits; circle descriptions
retain their prepared shift count. The same dictionary and canonical law
are used, with independent whole-player fresh-bit blocks. -/
namespace Blotto.GeneralPaperExactStoredSampler
open MeasureTheory
open GeneralPaperStoredStrategySampler (Sampler)
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

def shiftBits {n T K : ℕ} (sampler : Sampler n T K) : ℕ :=
  match sampler.description with
  | .circle _ _ _ => sampler.controls.shiftBits
  | .direct _ _ => 0

def shifts {n T K : ℕ} (sampler : Sampler n T K) : ℕ :=
  match sampler.description with
  | .circle _ _ _ => sampler.controls.shifts
  | .direct _ _ => 1

def bits {n T K : ℕ} (sampler : Sampler n T K) : ℕ := sampler.controls.rowBits + shiftBits sampler

theorem shifts_power {n T K : ℕ} (sampler : Sampler n T K) : shifts sampler = 2 ^ shiftBits sampler := by
  rcases sampler with ⟨o, b, controls, description⟩
  cases description with
  | circle hm hR rows => exact controls.shifts_power
  | direct hm columns => rfl

def run {n T K : ℕ} (bitModel : Bool) (primitive : ℕ → ℕ) (A : ℕ) (model : RationalCostModel) :
    (sampler : Sampler n T K) → (poor : Bool) → (Fin (bits sampler) → Bool) → GeneralPaperNativeFairSampler.Result n
  | ⟨o, b, controls, .circle _ hR rows⟩, poor, fresh =>
    let selected := GeneralPaperCachedCircleSampler.run bitModel primitive A
      controls.rowBits controls.shiftBits T controls.shifts
      (controls.rows_eq.symm.trans controls.rows_power) controls.shifts_power
      model o hR (if poor then b else 1) rows poor fresh
    {selected with work := selected.work + 128 * A}
  | ⟨_, b, controls, .direct hm columns⟩, poor, fresh =>
    let selected := GeneralPaperDirectRowExactSampler.run
      (GeneralPaperStrategyDescription.rationalPrice bitModel model)
      (GeneralPaperStrategyDescription.indexPrice bitModel) primitive A controls.rowBits T
      (controls.rows_eq.symm.trans controls.rows_power) hm
      (if poor then b else 1) (if poor then columns.poor else columns.rich) fresh
    {selected with work := selected.work + 128 * A}

noncomputable def law {n T K : ℕ} (bitModel : Bool) (primitive : ℕ → ℕ) (A : ℕ) (model : RationalCostModel)
    (sampler : Sampler n T K) (poor : Bool) : Mixed n :=
  (fairBitLaw (bits sampler)).map (fun fresh j => ((run bitModel primitive A model sampler poor fresh).output.read j : ℝ))

theorem fresh_reads {n T K : ℕ} (bitModel : Bool) (primitive : ℕ → ℕ) (A : ℕ) (model : RationalCostModel)
    (sampler : Sampler n T K) (poor : Bool) (fresh : Fin (bits sampler) → Bool) :
    (run bitModel primitive A model sampler poor fresh).freshReads = bits sampler := by
  rcases sampler with ⟨o, b, controls, description⟩
  cases description with
  | circle hm hR rows =>
    exact GeneralPaperCachedCircleSampler.fresh_reads bitModel primitive A controls.rowBits controls.shiftBits T controls.shifts
      (controls.rows_eq.symm.trans controls.rows_power) controls.shifts_power model o hR
      (if poor then b else 1) rows poor fresh
  | direct hm columns =>
    exact GeneralPaperDirectRowExactSampler.fresh_reads (GeneralPaperStrategyDescription.rationalPrice bitModel model)
      (GeneralPaperStrategyDescription.indexPrice bitModel) primitive A controls.rowBits T
      (controls.rows_eq.symm.trans controls.rows_power) hm (if poor then b else 1)
      (if poor then columns.poor else columns.rich) fresh

theorem logarithmic_bits {n T K : ℕ} (bitModel : Bool) (primitive : ℕ → ℕ) (A : ℕ) (model : RationalCostModel)
    (sampler : Sampler n T K) (poor : Bool) (fresh : Fin (bits sampler) → Bool) :
    (run bitModel primitive A model sampler poor fresh).freshReads = Nat.log2 (T * shifts sampler) := by
  have hp : T * shifts sampler = 2 ^ bits sampler := by
    calc
      _ = 2 ^ sampler.controls.rowBits * 2 ^ shiftBits sampler :=
        congrArg₂ Nat.mul (sampler.controls.rows_eq.symm.trans sampler.controls.rows_power) (shifts_power sampler)
      _ = _ := (pow_add _ _ _).symm
  rw [fresh_reads, hp, Nat.log2_two_pow]

theorem old_law {n T K : ℕ} (bitModel : Bool) (primitive : ℕ → ℕ) (A : ℕ) (model : RationalCostModel)
    (sampler : Sampler n T K) (poor : Bool) : law bitModel primitive A model sampler poor =
      GeneralPaperStoredStrategySampler.law bitModel primitive A model sampler poor := by
  rcases sampler with ⟨o, b, controls, description⟩
  rcases controls with ⟨rows, R, S, L, hRows, hT, hS⟩
  cases hRows
  cases description with
  | circle hm hR cached => rfl
  | direct hm columns =>
    change GeneralPaperDirectRowExactSampler.law _ _ primitive A R T hT hm _ _ =
      GeneralPaperDirectRowSampler.law _ _ primitive A R L T S hT hS hm _ _
    exact GeneralPaperDirectRowExactSampler.old_law _ _ primitive A R L T S hT hS hm _ _

theorem independent_players {n T K : ℕ} (bitModel : Bool) (primitive : ℕ → ℕ) (A : ℕ) (model : RationalCostModel)
    (sampler : Sampler n T K) :
    Measure.map (fun fresh =>
      ((fun j => ((run bitModel primitive A model sampler false (firstBitBlock (bits sampler) (bits sampler) fresh)).output.read j : ℝ)),
       (fun j => ((run bitModel primitive A model sampler true (secondBitBlock (bits sampler) (bits sampler) fresh)).output.read j : ℝ))))
      (fairBitLaw (bits sampler + bits sampler) : Measure (Fin (bits sampler + bits sampler) → Bool)) =
      (GeneralPaperStoredStrategySampler.law bitModel primitive A model sampler false : Measure (Allocation n)).prod
        (GeneralPaperStoredStrategySampler.law bitModel primitive A model sampler true : Measure (Allocation n)) := by
  rw [← old_law, ← old_law]
  exact fairBitBlocks_map_product (bits sampler) (bits sampler)
    (fun fresh j => ((run bitModel primitive A model sampler false fresh).output.read j : ℝ))
    (fun fresh j => ((run bitModel primitive A model sampler true fresh).output.read j : ℝ))

theorem shift_count_le {n T K : ℕ} (sampler : Sampler n T K) : shifts sampler ≤ sampler.controls.shifts := by
  rcases sampler with ⟨o, b, controls, description⟩
  cases description with
  | circle hm hR rows => exact le_rfl
  | direct hm columns =>
    change 1 ≤ controls.shifts
    rw [controls.shifts_power]
    exact Nat.one_le_two_pow

theorem every_output_feasible {n T K : ℕ} (bitModel : Bool) (primitive : ℕ → ℕ) (A : ℕ)
    (model : RationalCostModel) (sampler : Sampler n T K) (poor : Bool) (B : ℝ)
    (h : Supported B (GeneralPaperStoredStrategySampler.law bitModel primitive A model sampler poor))
    (fresh : Fin (bits sampler) → Bool) :
    Feasible B (fun j => ((run bitModel primitive A model sampler poor fresh).output.read j : ℝ)) := by
  have hn : Supported B (law bitModel primitive A model sampler poor) := by rw [old_law]; exact h
  change ∀ᵐ x ∂Measure.map
    (fun fresh j => ((run bitModel primitive A model sampler poor fresh).output.read j : ℝ))
    (fairBitLaw (bits sampler) : Measure (Fin (bits sampler) → Bool)), Feasible B x at hn
  rw [ae_map_iff (measurable_of_countable _).aemeasurable (measurable_feasible B)] at hn
  apply (ae_iff_of_countable.mp hn) fresh
  rw [fairBitLaw_singleton]
  positivity

end Blotto.GeneralPaperExactStoredSampler
