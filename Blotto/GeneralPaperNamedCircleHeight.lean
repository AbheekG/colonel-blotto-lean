import Blotto.GeneralPaperNamedCirclePrice

/-! Native named outputs have bounded rational encodings. The original
scale contributes only to the final product height; it is absent from
unit-row sorting, coefficients and circle selection. -/
namespace Blotto.GeneralPaperNamedCircleHeight
open GeneralPaperNamedCircleExecution GeneralPaperLightFieldIndexEquiv
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2400000

theorem assemble_height {n R : ℕ} (price index : ℕ → ℕ) (A : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (hR : 0<R) (c : ℚ) (prepared : Prepared state R) (chosen : FixedArrayTable state.light.size ℕ)
    (hBijective : Function.Bijective (mapping state)) (C K H : ℕ) (hc : RationalHeight c C)
    (hKept : ∀ i,RationalHeight (prepared.kept.read i) H)
    (hSorted : ∀ a,RationalHeight (prepared.sorted.read a) H)
    (hCoeff : ∀ j,RationalHeight (prepared.coefficients.read j) K) (j : Fin n) :
    RationalHeight ((assemble price index A state hR c prepared chosen).1.read j) (C+(K+H)) := by
  apply GeneralPaperRationalOutputScale.height price index A c _ C (K+H) hc
  apply GeneralPaperOriginalScatterLaw.height index A state _ _ hBijective (K+H)
  · intro i
    exact (hKept i).mono (by omega)
  · exact GeneralPaperNativeLightBids.height price index A hR prepared.coefficients prepared.sorted chosen K H hCoeff hSorted

theorem draw_height {n R : ℕ} (model : RationalCostModel) (W S : ℕ) (state : GeneralPaperLightFieldScan.State n)
    (hR : 0<R) (c : ℚ) (kept : FixedArrayTable state.heavy.size ℚ) (row : FixedArrayTable R ℚ)
    (weights : FixedArrayTable state.light.size ℕ) (hw : ∀ j,weights.read j≤W)
    (hBijective : Function.Bijective (mapping state)) (C H : ℕ) (hc : RationalHeight c C)
    (hKept : ∀ i,RationalHeight (kept.read i) H) (hRow : ∀ a,RationalHeight (row.read a) H) (l : Fin S) (j : Fin n) :
    RationalHeight ((drawArithmetic model W S state hR c
      (prepare (fun _ => 1) (fun _ => 1) 1 W state kept row weights).1 l).1.read j)
        (C+(binaryWordWidth R+2*binaryWordWidth W+H)) := by
  apply assemble_height _ _ _ state hR c _ _ hBijective C (binaryWordWidth R+2*binaryWordWidth W) H hc hKept
  · intro a
    change RationalHeight ((GeneralPaperNativeSortedRows.one (fun _ => 1) (fun _ => 1) 1 row).1.read a) H
    rw [GeneralPaperNativeSortedRows.one_data,FixedArrayTable.read_ofFn]
    exact hRow _
  · intro a
    change RationalHeight ((GeneralPaperCircleRationalCoefficients.run (fun _ => 1) (fun _ => 1) 1 R W weights).1.read a) _
    rw [GeneralPaperCircleRationalCoefficients.data,FixedArrayTable.read_ofFn]
    exact GeneralPaperCircleRationalCoefficients.ratio_height R W _ (hw a)

theorem assemble_models_data {n R : ℕ} (price price' index index' : ℕ → ℕ) (A A' : ℕ)
    (state : GeneralPaperLightFieldScan.State n) (hR : 0<R) (c : ℚ) (prepared : Prepared state R)
    (chosen : FixedArrayTable state.light.size ℕ) :
    (assemble price index A state hR c prepared chosen).1=(assemble price' index' A' state hR c prepared chosen).1 := by
  have hl : (GeneralPaperNativeLightBids.run price index A hR prepared.coefficients prepared.sorted chosen).1=
      (GeneralPaperNativeLightBids.run price' index' A' hR prepared.coefficients prepared.sorted chosen).1 := by
    rw [GeneralPaperNativeLightBids.data,GeneralPaperNativeLightBids.data]
  dsimp only [assemble]
  rw [GeneralPaperRationalOutputScale.data,GeneralPaperRationalOutputScale.data]
  rw [hl,GeneralPaperOriginalScatterLaw.models_data index index' A A' state prepared.kept]

end Blotto.GeneralPaperNamedCircleHeight
