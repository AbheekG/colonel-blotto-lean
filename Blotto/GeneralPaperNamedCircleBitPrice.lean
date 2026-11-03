import Blotto.GeneralPaperNamedCircleBitDraw

/-! Complete local bit price for named outputs and cached draws. The
original budget height appears only in final output products; all sort,
coefficient and circle-control work uses short unit-row inputs. -/
namespace Blotto.GeneralPaperNamedCircleBitPrice
open GeneralPaperNamedCircleExecution GeneralPaperLightFieldIndexEquiv
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def assembleProfile (model : RationalCostModel) (A C K H n : ℕ) : ℕ :=
  2*n*(model.rat (1+2*(K+H))+model.rat (1+2*(C+(K+H))))+1024*(n+1)*A

theorem assemble_work {n R : ℕ} (model : RationalCostModel) (A C K H : ℕ) (hA : 1≤A)
    (state : GeneralPaperLightFieldScan.State n) (hR : 0<R) (c : ℚ) (prepared : Prepared state R)
    (chosen : FixedArrayTable state.light.size ℕ) (hBijective : Function.Bijective (mapping state))
    (hc : RationalHeight c C) (hKept : ∀ i,RationalHeight (prepared.kept.read i) H)
    (hSorted : ∀ a,RationalHeight (prepared.sorted.read a) H)
    (hCoeff : ∀ j,RationalHeight (prepared.coefficients.read j) K) (hChosen : ∀ j,chosen.read j<R)
    (hCapacity : 1+binaryWordWidth (2*n+R+2)≤A) :
    (assemble model.rat (fun w => w) A state hR c prepared chosen).2≤assembleProfile model A C K H n := by
  have hSize := GeneralPaperOriginalScatterLaw.size state hBijective
  have hg : state.light.size≤n := by omega
  have hi (i : ℕ) (hi : i≤2*n+R+1) : binaryWordWidth (i+1)≤A :=
    (binaryWordWidth_mono (by omega : i+1≤2*n+R+2)).trans (by omega)
  have hControl : 1+binaryWordWidth (state.heavy.size+state.light.size)≤A := by
    rw [hSize]
    exact (Nat.add_le_add_left (binaryWordWidth_mono (by omega : n≤2*n+R+2)) 1).trans hCapacity
  let light := GeneralPaperNativeLightBids.run model.rat (fun w => w) A hR prepared.coefficients prepared.sorted chosen
  let named := GeneralPaperOriginalFieldScatter.run (fun w => w) A state prepared.kept light.1
  have hl := GeneralPaperNativeLightBids.work model.rat (fun w => w) model.monotone A K H hA hR prepared.coefficients
    prepared.sorted chosen hCoeff hSorted hChosen (fun i hh => hi i (by omega)) (fun i hh => hi i (by omega))
  have hn := GeneralPaperOriginalFieldScatter.work (fun w => w) (fun _ _ hh => hh) A hA state prepared.kept light.1 hControl
    (fun i hh => hi i (by omega))
  have hNamed : ∀ j,RationalHeight (named.1.read j) (K+H) :=
    GeneralPaperOriginalScatterLaw.height (fun w => w) A state prepared.kept light.1 hBijective (K+H)
      (fun i => (hKept i).mono (by omega))
      (GeneralPaperNativeLightBids.height model.rat (fun w => w) A hR prepared.coefficients prepared.sorted chosen K H hCoeff hSorted)
  have hs := GeneralPaperRationalOutputScale.work model.rat (fun w => w) model.monotone A C (K+H) hA c named.1 hc hNamed
    (fun i hh => hi i (by omega))
  rw [hSize,show n+state.heavy.size+state.light.size+1=n+n+1 by omega] at hn
  have hgA := Nat.mul_le_mul_right A hg
  have hgP := Nat.mul_le_mul_right (model.rat (1+2*(K+H))) hg
  change light.2≤_ at hl
  change named.2≤_ at hn
  change light.2+named.2+(GeneralPaperRationalOutputScale.run model.rat (fun w => w) A c named.1).2+32*A≤_
  unfold assembleProfile
  nlinarith only [hl,hn,hs,hgA,hgP,Nat.zero_le (n*A),Nat.zero_le A]

def drawProfile (model : RationalCostModel) (A R W S C H n g : ℕ) : ℕ :=
  GeneralPaperNativeChoiceArrayBits.profile model A R W S g+
    assembleProfile model A C (binaryWordWidth R+2*binaryWordWidth W) H n+32*A

theorem draw_work {n R : ℕ} (model : RationalCostModel) (A W S C H : ℕ) (hA : 1≤A)
    (state : GeneralPaperLightFieldScan.State n) (hR : 0<R) (hW : 0<W) (hS : 0<S) (c : ℚ)
    (price index : ℕ → ℕ) (Ap : ℕ) (kept : FixedArrayTable state.heavy.size ℚ)
    (row : FixedArrayTable R ℚ) (weights : FixedArrayTable state.light.size ℕ) (hs : ∑ j,weights.read j=W)
    (hBijective : Function.Bijective (mapping state)) (hc : RationalHeight c C)
    (hKept : ∀ i,RationalHeight (kept.read i) H) (hRow : ∀ a,RationalHeight (row.read a) H)
    (hCapacity : 1+binaryWordWidth (2*n+R+2)≤A) (l : Fin S) :
    (GeneralPaperNamedCircleBitDraw.run model A W S state hR c (prepare price index Ap W state kept row weights).1 l).2≤
      drawProfile model A R W S C H n state.light.size := by
  let prepared := (prepare price index Ap W state kept row weights).1
  let chosen := GeneralPaperNativeChoiceArrayBits.run model (fun w => w) A R W S l.val prepared.metadata
  have hSize := GeneralPaperOriginalScatterLaw.size state hBijective
  have hg : state.light.size≤n := by omega
  have hIndex : binaryWordWidth (state.light.size+1)≤A :=
    (binaryWordWidth_mono (by omega : state.light.size+1≤2*n+R+2)).trans (by omega)
  have hcRun := GeneralPaperNativeChoiceArrayBits.work model A R W S l.val hR hW hS l.isLt price Ap weights hs hA hIndex
  have hChoices (j : Fin state.light.size) : chosen.1.read j<R := by
    dsimp only [chosen,prepared,prepare]
    rw [GeneralPaperNativeChoiceArrayBits.data]
    exact GeneralPaperNativeChoiceArray.bounded model price Ap R W S hR hW hS l weights hs j
  have hSorted (a : Fin R) : RationalHeight (prepared.sorted.read a) H := by
    change RationalHeight ((GeneralPaperNativeSortedRows.one price index Ap row).1.read a) H
    rw [GeneralPaperNativeSortedRows.one_data,FixedArrayTable.read_ofFn]
    exact hRow _
  have hWeights (j : Fin state.light.size) : weights.read j≤W := by
    rw [←hs]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hCoeff (j : Fin state.light.size) : RationalHeight (prepared.coefficients.read j) (binaryWordWidth R+2*binaryWordWidth W) := by
    change RationalHeight ((GeneralPaperCircleRationalCoefficients.run price index Ap R W weights).1.read j) _
    rw [GeneralPaperCircleRationalCoefficients.data,FixedArrayTable.read_ofFn]
    exact GeneralPaperCircleRationalCoefficients.ratio_height R W _ (hWeights j)
  have ho := assemble_work model A C (binaryWordWidth R+2*binaryWordWidth W) H hA state hR c prepared chosen.1
    hBijective hc hKept hSorted hCoeff hChoices hCapacity
  change chosen.2≤_ at hcRun
  change chosen.2+(assemble model.rat (fun w => w) A state hR c prepared chosen.1).2+32*A≤_
  unfold drawProfile
  exact Nat.add_le_add_right (Nat.add_le_add hcRun ho) _

end Blotto.GeneralPaperNamedCircleBitPrice
