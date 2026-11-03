import Blotto.GeneralPaperOriginalScatterModels

/-! Once-only row preparation and named rational output assembly. Draws
reuse the stored sort, coefficients, kept references and arc metadata. The
arithmetic draw executes the selected shift once. Complete draw bit/space
and fair-bit sampling joins are separate obligations. -/
namespace Blotto.GeneralPaperNamedCircleExecution
set_option autoImplicit false
set_option maxHeartbeats 1600000

structure Prepared {n : ℕ} (state : GeneralPaperLightFieldScan.State n) (R : ℕ) where
  kept : FixedArrayTable state.heavy.size ℚ
  sorted : FixedArrayTable R ℚ
  coefficients : FixedArrayTable state.light.size ℚ
  metadata : GeneralPaperNativeChoiceArray.Prepared state.light.size

def prepare {n R : ℕ} (price index : ℕ → ℕ) (A W : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (kept : FixedArrayTable state.heavy.size ℚ) (row : FixedArrayTable R ℚ)
    (weights : FixedArrayTable state.light.size ℕ) : Prepared state R × ℕ :=
  let sorted := GeneralPaperNativeSortedRows.one price index A row
  let coefficients := GeneralPaperCircleRationalCoefficients.run price index A R W weights
  let metadata := GeneralPaperNativeChoiceArray.prepare price A R weights
  (⟨kept,sorted.1,coefficients.1,metadata.1⟩,sorted.2+coefficients.2+metadata.2+128*A)

def assemble {n R : ℕ} (price index : ℕ → ℕ) (A : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (hR : 0<R) (c : ℚ) (prepared : Prepared state R) (chosen : FixedArrayTable state.light.size ℕ) : FixedArrayTable n ℚ × ℕ :=
  let light := GeneralPaperNativeLightBids.run price index A hR prepared.coefficients prepared.sorted chosen
  let named := GeneralPaperOriginalFieldScatter.run index A state prepared.kept light.1
  let scaled := GeneralPaperRationalOutputScale.run price index A c named.1
  (scaled.1,light.2+named.2+scaled.2+32*A)

def drawArithmetic {n R : ℕ} (model : RationalCostModel) (W S : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (hR : 0<R) (c : ℚ) (prepared : Prepared state R) (l : Fin S) : FixedArrayTable n ℚ × ℕ :=
  let chosen := GeneralPaperNativeChoiceArray.draw model R W S l.val prepared.metadata
  let output := assemble (fun _ => 1) (fun _ => 1) 1 state hR c prepared chosen.1
  (output.1,chosen.2+output.2+16)

theorem prepare_kept {n R : ℕ} (price index : ℕ → ℕ) (A W : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (kept : FixedArrayTable state.heavy.size ℚ) (row : FixedArrayTable R ℚ) (weights : FixedArrayTable state.light.size ℕ) :
    (prepare price index A W state kept row weights).1.kept=kept := rfl

theorem prepare_sorted {n R : ℕ} (price index : ℕ → ℕ) (A W : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (kept : FixedArrayTable state.heavy.size ℚ) (row : FixedArrayTable R ℚ) (weights : FixedArrayTable state.light.size ℕ) (a : Fin R) :
    ((prepare price index A W state kept row weights).1.sorted.read a:ℝ)=
      GeneralPaperCircleSortedComparison.sorted (fun j => (row.read j:ℝ)) a :=
  GeneralPaperNativeSortedRows.one_real price index A row a

end Blotto.GeneralPaperNamedCircleExecution
