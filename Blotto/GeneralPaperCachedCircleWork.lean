import Blotto.GeneralPaperCachedCircleSampler

/-! Work for the actual shared-cache constructor. Light-field coefficients
and metadata are built once, outside both row loops. Each row extracts and
sorts representative references only. Heights and capacities below are
erased bounds, never native encoding or work-census passes. -/
namespace Blotto.GeneralPaperCachedCircleWork
open GeneralPaperCachedCircleRows
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 6500000
set_option maxRecDepth 16384

theorem index_bound (index : ℕ → ℕ) (hMono : Monotone index) (N A : ℕ)
    (hCap : index (1+binaryWordWidth (N+1))≤A) (i : ℕ) (hi : i≤N) :
    index (binaryWordWidth (i+1))≤A :=
  (hMono ((binaryWordWidth_mono (Nat.add_le_add_right hi 1)).trans (by omega))).trans hCap

def commonProfile (g R W A : ℕ) (price : ℕ → ℕ) : ℕ :=
  g*(5*price (GeneralPaperCircleRationalCoefficients.width R W)+64*A)+44*(g+1)*A+
    price (GeneralPaperCircleRationalCoefficients.width R W)+16*A+
    (g+1)*(96*A+8*price (1+binaryWordWidth (R*W+R+W+1)))+64*A

theorem common_work {g : ℕ} (price index : ℕ → ℕ) (hMono : Monotone price) (A R W : ℕ) (hA : 1≤A)
    (weights : FixedArrayTable g ℕ) (hw : ∀ j,weights.read j≤W) (hs : ∑ j,weights.read j=W)
    (hIndex : ∀ i≤g,index (binaryWordWidth (i+1))≤A) :
    (GeneralPaperCachedCircleCommon.run price index A R W weights).2≤commonProfile g R W A price := by
  have hc := GeneralPaperCircleRationalCoefficients.work price index hMono A R W hA weights hw hIndex
  have hm := GeneralPaperCircleArcMetadata.work_bound price hMono A R (List.ofFn weights.read) 0
    (R*W+R+W+1) (by omega) (by rw [List.sum_ofFn,hs];omega) (by
      intro w hmem
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hmem
      exact (hw j).trans (by omega))
  rw [List.length_ofFn] at hm
  unfold GeneralPaperCachedCircleCommon.run GeneralPaperNativeChoiceArray.prepare commonProfile
  dsimp only
  nlinarith only [hc,hm]

theorem common_arithmetic {g : ℕ} (R W : ℕ) (weights : FixedArrayTable g ℕ)
    (hw : ∀ j,weights.read j≤W) (hs : ∑ j,weights.read j=W) :
    (GeneralPaperCachedCircleCommon.run (fun _ => 1) (fun _ => 1) 1 R W weights).2≤217*g+229 := by
  have h := common_work (fun _ => 1) (fun _ => 1) (fun _ _ _ => le_rfl) 1 R W (by decide) weights hw hs (fun _ _ => le_rfl)
  simp only [commonProfile,Nat.mul_one] at h
  omega

def originalCommonProfile (g R W A : ℕ) (price : ℕ → ℕ) : ℕ :=
  g*(64*A)+44*(g+1)*A+commonProfile g R W A price+64*A

theorem original_common_work {n : ℕ} (price index : ℕ → ℕ) (hMono : Monotone price) (A : ℕ) (hA : 1≤A)
    (o : GeneralPaperReducedValuesDriver.Output n) (hConserved : GeneralPaperCircleActualWeights.Conserved o)
    (hIndex : ∀ i≤o.classified.light.size,index (binaryWordWidth (i+1))≤A) :
    (GeneralPaperCachedCircleCommon.fromOriginal price index A o).2≤
      originalCommonProfile o.classified.light.size o.representatives o.classified.lightWeight A price := by
  have hs : ∑ j,(GeneralPaperNativeLightWeights.run index A o).1.read j=o.classified.lightWeight := by
    rw [GeneralPaperNativeLightWeights.data]
    simpa only [GeneralPaperCircleActualWeights.Conserved,FixedArrayTable.read_ofFn] using hConserved
  have hw : ∀ j,(GeneralPaperNativeLightWeights.run index A o).1.read j≤o.classified.lightWeight := by
    rw [←hs]
    intro j
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have ha := GeneralPaperNativeLightWeights.work index A hA o hIndex
  have hc := common_work price index hMono A o.representatives o.classified.lightWeight hA
    (GeneralPaperNativeLightWeights.run index A o).1 hw hs hIndex
  unfold GeneralPaperCachedCircleCommon.fromOriginal originalCommonProfile
  dsimp only
  omega

theorem original_common_arithmetic {n : ℕ} (o : GeneralPaperReducedValuesDriver.Output n)
    (hConserved : GeneralPaperCircleActualWeights.Conserved o) :
    (GeneralPaperCachedCircleCommon.fromOriginal (fun _ => 1) (fun _ => 1) 1 o).2≤325*o.classified.light.size+337 := by
  have h := original_common_work (fun _ => 1) (fun _ => 1) (fun _ _ _ => le_rfl) 1 (by decide) o hConserved (fun _ _ => le_rfl)
  simp only [originalCommonProfile,commonProfile,Nat.mul_one] at h
  omega

def representativesProfile (R A : ℕ) : ℕ := R*(130*A)+44*(R+1)*A

theorem representatives_work {T h R K : ℕ} (index : ℕ → ℕ) (hMono : Monotone index) (A N : ℕ) (hA : 1≤A)
    (hSize : h+R≤N) (hCap : index (1+binaryWordWidth (N+1))≤A)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T) :
    (representatives index A columns i).2≤representativesProfile R A := by
  unfold representatives representativesProfile
  apply GeneralPaperControlArrayPrice.indexed_work index A (130*A) _ hA
  · intro j hj
    exact index_bound index hMono N A hCap j (by omega)
  · intro a
    have h := GeneralPaperNaturalPrimitivePrice.binary_le index hMono (fun a b => a+b) h a.val (N+1)
      (by omega) (by omega) (by omega)
    nlinarith only [h,hCap]

def rowProfile (R A P : ℕ) : ℕ :=
  representativesProfile R A+GeneralPaperNativeSortedRows.oneProfile R A P+64*A

theorem row_work {T h R K : ℕ} (price index : ℕ → ℕ) (hMono : Monotone price) (hIMono : Monotone index)
    (A N H : ℕ) (hA : 1≤A) (hSize : h+R≤N) (hCap : index (1+binaryWordWidth (N+1))≤A)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K))
    (hColumns : ∀ j a,rationalWordWidth ((columns.read j).anchors.read a)≤H) (i : Fin T) :
    (sortedRow price index A columns i).2≤rowProfile R A (price H) := by
  have he := representatives_work index hIMono A N hA hSize hCap columns i
  have hs := GeneralPaperNativeSortedRows.one_work price index hMono A H hA (representatives index A columns i).1
    (by intro a;rw [representatives_data,FixedArrayTable.read_ofFn];exact hColumns _ _)
    (fun j hj => index_bound index hIMono N A hCap j (by omega))
  unfold sortedRow rowProfile
  dsimp only
  omega

def rowsProfile (T R A P : ℕ) : ℕ := T*(rowProfile R A P+64*A)+44*(T+1)*A+64*A

theorem rows_work {T h R K : ℕ} (price index : ℕ → ℕ) (hMono : Monotone price) (hIMono : Monotone index)
    (A N H : ℕ) (hA : 1≤A) (hSize : h+R≤N) (hT : T≤N) (hCap : index (1+binaryWordWidth (N+1))≤A)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K))
    (hColumns : ∀ j a,rationalWordWidth ((columns.read j).anchors.read a)≤H) :
    (prepare price index A columns).2≤rowsProfile T R A (price H) := by
  have ha := GeneralPaperControlArrayPrice.indexed_work index A (rowProfile R A (price H)+64*A)
    (fun i : Fin T => let row := sortedRow price index A columns i;(row.1,row.2+64*A)) hA
    (fun j hj => index_bound index hIMono N A hCap j (hj.trans hT))
    (fun i => Nat.add_le_add_right (row_work price index hMono hIMono A N H hA hSize hCap columns hColumns i) _)
  unfold prepare sortedRows rowsProfile
  dsimp only at ha ⊢
  omega

theorem row_arithmetic {T h R K : ℕ} (model : RationalCostModel)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K)) (i : Fin T) :
    (sortedRow (fun _ => 1) (fun _ => 1) 1 columns i).2≤rowProfile R 1 1 := by
  have he := representatives_work (fun _ => 1) (fun _ _ _ => le_rfl) 1 (h+R) (by decide) le_rfl le_rfl columns i
  have hs := GeneralPaperNativeSortedModels.one_arithmetic_work model (representatives (fun _ => 1) 1 columns i).1
  change (GeneralPaperNativeSortedRows.one (fun _ => 1) (fun _ => 1) 1 (representatives (fun _ => 1) 1 columns i).1).2≤_ at hs
  unfold sortedRow rowProfile
  dsimp only
  omega

theorem rows_arithmetic {T h R K : ℕ} (model : RationalCostModel)
    (columns : FixedArrayTable (h+R) (GeneralPaperQuantizedColumn.Column T K)) :
    (prepare (fun _ => 1) (fun _ => 1) 1 columns).2≤rowsProfile T R 1 1 := by
  have ha := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 (rowProfile R 1 1+64)
    (fun i : Fin T => let row := sortedRow (fun _ => 1) (fun _ => 1) 1 columns i;(row.1,row.2+64))
    (by decide) (fun _ _ => le_rfl) (fun i => Nat.add_le_add_right (row_arithmetic model columns i) 64)
  unfold prepare sortedRows rowsProfile
  dsimp only
  simpa only [Nat.mul_one] using Nat.add_le_add_right ha 64

def selectedProfile (h A : ℕ) : ℕ := h*(128*A)+44*(h+1)*A+64*A

theorem selected_work {T n R K : ℕ} (index : ℕ → ℕ) (A : ℕ) (hA : 1≤A)
    (state : GeneralPaperLightFieldScan.State n) (rows : Rows T state.heavy.size R K)
    (common : GeneralPaperCachedCircleCommon.Cache state.light.size) (i : Fin T)
    (hIndex : ∀ j≤state.heavy.size,index (binaryWordWidth (j+1))≤A) :
    (materialize index A state rows common i).2≤selectedProfile state.heavy.size A := by
  have h := GeneralPaperControlArrayPrice.indexed_work index A (128*A)
    (fun j : Fin state.heavy.size =>
      let column := rows.columns.read (Fin.castAdd R j)
      (column.anchors.read (column.labels.read i),128*A)) hA hIndex (fun _ => le_rfl)
  unfold materialize kept selectedProfile
  dsimp only at h ⊢
  omega

def pairProfile (T g R W A : ℕ) (price : ℕ → ℕ) (H : ℕ) : ℕ :=
  originalCommonProfile g R W A price+2*rowsProfile T R A (price H)+128*A

theorem pair_work {n T K : ℕ} (price index : ℕ → ℕ) (hMono : Monotone price) (hIMono : Monotone index)
    (A N H : ℕ) (hA : 1≤A) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : o.m=o.classified.heavy.size+o.representatives) (hConserved : GeneralPaperCircleActualWeights.Conserved o)
    (columns : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K)
    (hSize : o.classified.heavy.size+o.representatives≤N) (hT : T≤N) (hg : o.classified.light.size≤N)
    (hCap : index (1+binaryWordWidth (N+1))≤A)
    (hRich : ∀ j a,rationalWordWidth (((GeneralPaperPhysicalFieldCast.columns hm columns.rich).read j).anchors.read a)≤H)
    (hPoor : ∀ j a,rationalWordWidth (((GeneralPaperPhysicalFieldCast.columns hm columns.poor).read j).anchors.read a)≤H) :
    (pair price index A o hm columns).2≤pairProfile T o.classified.light.size o.representatives o.classified.lightWeight A price H := by
  have hc := original_common_work price index hMono A hA o hConserved
    (fun j hj => index_bound index hIMono N A hCap j (hj.trans hg))
  have hr := rows_work price index hMono hIMono A N H hA hSize hT hCap
    (GeneralPaperPhysicalFieldCast.columns hm columns.rich) hRich
  have hp := rows_work price index hMono hIMono A N H hA hSize hT hCap
    (GeneralPaperPhysicalFieldCast.columns hm columns.poor) hPoor
  unfold pair pairProfile
  dsimp only
  omega

theorem pair_arithmetic {n T K : ℕ} (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n)
    (hm : o.m=o.classified.heavy.size+o.representatives) (hConserved : GeneralPaperCircleActualWeights.Conserved o)
    (columns : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K) :
    (pair (fun _ => 1) (fun _ => 1) 1 o hm columns).2≤325*o.classified.light.size+465+2*rowsProfile T o.representatives 1 1 := by
  have hc := original_common_arithmetic o hConserved
  have hr := rows_arithmetic model (GeneralPaperPhysicalFieldCast.columns hm columns.rich)
  have hp := rows_arithmetic model (GeneralPaperPhysicalFieldCast.columns hm columns.poor)
  unfold pair
  dsimp only
  omega

theorem original_pair_arithmetic {n T K : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (input : FixedArrayTable n ℚ)
    (hm : (GeneralPaperOriginalValueReduction.run bits model W k input).1.m=
      (GeneralPaperOriginalValueReduction.run bits model W k input).1.classified.heavy.size+
        (GeneralPaperOriginalValueReduction.run bits model W k input).1.representatives)
    (columns : GeneralPaperOriginalDrawEquilibrium.Columns T (GeneralPaperOriginalValueReduction.run bits model W k input).1.m K) :
    let o := (GeneralPaperOriginalValueReduction.run bits model W k input).1
    (pair (fun _ => 1) (fun _ => 1) 1 o hm columns).2≤325*o.classified.light.size+465+2*rowsProfile T o.representatives 1 1 :=
  pair_arithmetic model _ hm (GeneralPaperCircleActualWeights.original_sum bits model W k input) columns

end Blotto.GeneralPaperCachedCircleWork
