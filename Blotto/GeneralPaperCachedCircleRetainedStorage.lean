import Blotto.GeneralPaperSamplingFastBitBound

/-! Retained shared circle owners and sorted references. The complete
source columns own rational anchors; every sorted rational reference has a
proved origin in those columns. No T-fold light-field cache is counted. -/
namespace Blotto.GeneralPaperCachedCircleRetainedStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open GeneralPaperEnclosingSourceOwners GeneralPaperCachedCircleRows
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384

def arcBits (W : ℕ) (arc : ℕ×ℕ) : ℕ := natBits arc.1+natBits arc.2+32*W

def commonFoot {g : ℕ} (W : ℕ) (cache : GeneralPaperCachedCircleCommon.Cache g) : ℕ :=
  arrayFootprint W natBits cache.weights+arrayFootprint W rationalWordWidth cache.coefficients+
    listFootprint W (arcBits W) cache.metadata.arcs+64*W

def commonProfile (W g R mass : ℕ) : ℕ :=
  arrayProfile W g (natBits mass)+arrayProfile W g (1+2*(binaryWordWidth R+2*binaryWordWidth mass))+
    g*(2*natBits (R*mass)+34*W)+96*W

theorem common_bound {g : ℕ} (price index : ℕ → ℕ) (A W R mass : ℕ) (weights : FixedArrayTable g ℕ)
    (hs : ∑ j,weights.read j=mass) :
    commonFoot W (GeneralPaperCachedCircleCommon.run price index A R mass weights).1≤commonProfile W g R mass := by
  have hw (j : Fin g) : weights.read j≤mass := by
    rw [←hs]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hWeights := array_bound W (natBits mass) natBits weights
    (fun j => Nat.add_le_add_left (binaryWordWidth_mono (hw j)) 1)
  have hCoefficients := array_bound W (1+2*(binaryWordWidth R+2*binaryWordWidth mass)) rationalWordWidth
    (GeneralPaperCachedCircleCommon.run price index A R mass weights).1.coefficients (by
      intro j
      rw [GeneralPaperCachedCircleCommon.coefficients_data,FixedArrayTable.read_ofFn]
      exact rationalWordWidth_of_height (GeneralPaperCircleRationalCoefficients.ratio_height R mass _ (hw j)))
  let cache := (GeneralPaperCachedCircleCommon.run price index A R mass weights).1
  have hArcs (arc : ℕ×ℕ) (ha : arc∈cache.metadata.arcs) : arc.1+arc.2≤R*mass := by
    have h := GeneralPaperCircleArcMetadata.ranges price A R (List.ofFn weights.read) 0 arc ha
    rw [GeneralPaperCircleArcMetadata.total,List.sum_ofFn,hs,Nat.zero_add] at h
    exact h
  have hList := list_bound W (2*natBits (R*mass)+32*W) (arcBits W) cache.metadata.arcs (by
    intro arc ha
    have h := hArcs arc ha
    have h1 := binaryWordWidth_mono (show arc.1≤R*mass by omega)
    have h2 := binaryWordWidth_mono (show arc.2≤R*mass by omega)
    unfold arcBits natBits
    omega)
  rw [cache.metadata.count] at hList
  unfold commonFoot commonProfile
  rw [GeneralPaperCachedCircleCommon.weights_data]
  change _≤_ at hCoefficients
  dsimp only [cache] at hList
  nlinarith only [hWeights,hCoefficients,hList]

def referenceRowsFoot {T R : ℕ} (W : ℕ) (rows : FixedArrayTable T (FixedArrayTable R ℚ)) : ℕ :=
  arrayFootprint W (arrayFootprint W (fun _ : ℚ => 0)) rows

def referenceRowsProfile (W T R : ℕ) : ℕ := arrayProfile W T (arrayProfile W R 0)

theorem reference_rows_bound {T R : ℕ} (W : ℕ) (rows : FixedArrayTable T (FixedArrayTable R ℚ)) :
    referenceRowsFoot W rows≤referenceRowsProfile W T R :=
  array_bound W _ _ rows (fun i => array_bound W 0 (fun _ : ℚ => 0) (rows.read i) (fun _ => le_rfl))

theorem sorted_reference_origin {T h R K : ℕ} (price index : ℕ → ℕ) (A : ℕ)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T) (a : Fin R) :
    ∃ j : Fin (h+R),((prepare price index A columns).1.sorted.read i).read a=
      (columns.read j).anchors.read ((columns.read j).labels.read i) := by
  change ∃ j,((sortedRows price index A columns).1.read i).read a=_
  rw [read_sorted]
  exact sorted_origin price index A columns i a

def rowsFoot {T h R K : ℕ} (W : ℕ) (rows : Rows T h R K) : ℕ :=
  columnsFoot W rows.columns+referenceRowsFoot W rows.sorted+32*W

def rowsProfile (W T h R K H : ℕ) : ℕ :=
  columnsProfile W T (h+R) K (1+2*H)+referenceRowsProfile W T R+32*W

theorem rows_bound {T h R K : ℕ} (price index : ℕ → ℕ) (A W H : ℕ)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K))
    (hColumns : ∀ j l,RationalHeight ((columns.read j).anchors.read l) H) :
    rowsFoot W (prepare price index A columns).1≤rowsProfile W T h R K H := by
  have hc := columns_bound W (1+2*H) columns (fun j l => rationalWordWidth_of_height (hColumns j l))
  have hr := reference_rows_bound W (prepare price index A columns).1.sorted
  unfold rowsFoot rowsProfile
  rw [columns_data]
  omega

def pairFoot {n T R K : ℕ} (W : ℕ) (state : GeneralPaperLightFieldScan.State n) (cached : Pair T R K state) : ℕ :=
  commonFoot W cached.common+rowsFoot W cached.rich+rowsFoot W cached.poor+32*W

def pairProfile (W T h g R mass K H : ℕ) : ℕ :=
  commonProfile W g R mass+2*rowsProfile W T h R K H+32*W

theorem pair_bound {n T K : ℕ} (price index : ℕ → ℕ) (A W H : ℕ)
    (o : GeneralPaperReducedValuesDriver.Output n) (hm : o.m=o.classified.heavy.size+o.representatives)
    (physical : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K)
    (hConserved : GeneralPaperCircleActualWeights.Conserved o)
    (hRich : ∀ j l,RationalHeight ((physical.rich.read j).anchors.read l) H)
    (hPoor : ∀ j l,RationalHeight ((physical.poor.read j).anchors.read l) H) :
    pairFoot W o.classified (pair price index A o hm physical).1≤
      pairProfile W T o.classified.heavy.size o.classified.light.size o.representatives o.classified.lightWeight K H := by
  have hs : ∑ j,(GeneralPaperNativeLightWeights.run index A o).1.read j=o.classified.lightWeight := by
    rw [GeneralPaperNativeLightWeights.data]
    simpa only [GeneralPaperCircleActualWeights.Conserved,FixedArrayTable.read_ofFn] using hConserved
  have hc := common_bound price index A W o.representatives o.classified.lightWeight (GeneralPaperNativeLightWeights.run index A o).1 hs
  have hr := rows_bound price index A W H (GeneralPaperPhysicalFieldCast.columns hm physical.rich)
    (GeneralPaperPhysicalFieldCast.height hm physical.rich H hRich)
  have hp := rows_bound price index A W H (GeneralPaperPhysicalFieldCast.columns hm physical.poor)
    (GeneralPaperPhysicalFieldCast.height hm physical.poor H hPoor)
  unfold pairFoot pairProfile GeneralPaperCachedCircleRows.pair GeneralPaperCachedCircleCommon.fromOriginal
  dsimp only at hc hr hp ⊢
  omega

end Blotto.GeneralPaperCachedCircleRetainedStorage
