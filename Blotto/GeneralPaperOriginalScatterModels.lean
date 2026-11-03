import Blotto.GeneralPaperRationalOutputScale

/-! Derived model prices for original-field writes. Address/control words
come from the actual retained array sizes. Rational payloads are copied as
references here; their final scaled output products have separate prices. -/
namespace Blotto.GeneralPaperOriginalScatterModels
open GeneralPaperSourceRowsExecution GeneralPaperSummaryArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 1600000

def run {n : ℕ} (bits : Bool) (W : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (kept : FixedArrayTable state.heavy.size ℚ) (light : FixedArrayTable state.light.size ℚ) : FixedArrayTable n ℚ × ℕ :=
  GeneralPaperOriginalFieldScatter.run (index bits) (address bits W (n+state.heavy.size+state.light.size)) state kept light

theorem models_data {n : ℕ} (W : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (kept : FixedArrayTable state.heavy.size ℚ) (light : FixedArrayTable state.light.size ℚ) :
    (run true W state kept light).1=(run false 1 state kept light).1 :=
  GeneralPaperOriginalScatterLaw.models_data _ _ _ _ state kept light

theorem bit_work {n : ℕ} (W : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (kept : FixedArrayTable state.heavy.size ℚ) (light : FixedArrayTable state.light.size ℚ)
    (hBijective : Function.Bijective (GeneralPaperLightFieldIndexEquiv.mapping state)) :
    (run true W state kept light).2≤451*(n+1)*arrayWord W (n+state.heavy.size+state.light.size) := by
  have hs := GeneralPaperOriginalScatterLaw.size state hBijective
  have h := GeneralPaperOriginalFieldScatter.work (fun w => w) (fun _ _ h => h) _
    (GeneralPaperSummaryArrayControls.array_word_positive W _) state kept light
    (GeneralPaperReducedValueArrayPrice.control_word W _ _ (by omega))
    (GeneralPaperSummaryArrayControls.array_index W _)
  change (GeneralPaperOriginalFieldScatter.run (fun w => w)
    (arrayWord W (n+state.heavy.size+state.light.size)) state kept light).2≤_
  have hsA := congrArg (fun x => x*arrayWord W (n+state.heavy.size+state.light.size)) hs
  nlinarith only [h,hsA]

theorem arithmetic_work {n : ℕ} (state : GeneralPaperLightFieldScan.State n)
    (kept : FixedArrayTable state.heavy.size ℚ) (light : FixedArrayTable state.light.size ℚ)
    (hBijective : Function.Bijective (GeneralPaperLightFieldIndexEquiv.mapping state)) :
    (run false 1 state kept light).2≤451*(n+1) := by
  have hs := GeneralPaperOriginalScatterLaw.size state hBijective
  have h := GeneralPaperOriginalFieldScatter.work (fun _ => 1) (fun _ _ _ => le_rfl) 1 (by decide)
    state kept light (by decide) (fun _ _ => le_rfl)
  change (GeneralPaperOriginalFieldScatter.run (fun _ => 1) 1 state kept light).2≤_
  nlinarith only [h,hs]

end Blotto.GeneralPaperOriginalScatterModels
