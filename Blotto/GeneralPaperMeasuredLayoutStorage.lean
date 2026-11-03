import Blotto.GeneralPaperCompleteFramedPreparationWork

/-! Erased ownership observers for the actual size plans and allocated
region lists. Encoded starts/lengths, fixed-width target references, list
links, record descriptors and saved work fields are explicit. These are
temporary construction owners; no observer is executed by preparation. -/
namespace Blotto.GeneralPaperMeasuredLayoutStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperSequentialLayout
open GeneralPaperMeasuredBlockPlan (Plan)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def regionFoot {A : ℕ} (S : ℕ) (region : Region A) : ℕ :=
  fields S [region.start,region.length] + A + 64 * S

def regionBound (S A : ℕ) : ℕ := 128 * (S + A + 1)

theorem region_bound (S A : ℕ) (region : Region A) (hA : 0 < A)
    (hCap : region.stop < 2 ^ A) : regionFoot S region ≤ regionBound S A := by
  have hStart := binaryWordWidth_le_of_lt_pow hA (show region.start < 2 ^ A by unfold Region.stop at hCap; omega)
  have hLength := binaryWordWidth_le_of_lt_pow hA (show region.length < 2 ^ A by unfold Region.stop at hCap; omega)
  unfold regionFoot regionBound fields natBits
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  omega

def planFoot (S : ℕ) (plan : Plan) : ℕ :=
  listFootprint S natBits plan.sizes + fields S [plan.work] + 64 * S

def planBound (S A B P : ℕ) : ℕ :=
  B * (A + 2 * S + 1) + natBits P + 129 * S

theorem plan_bound (S A : ℕ) (plan : Plan)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A)
    (hCap : plan.sizes.sum < 2 ^ A) (P : ℕ) (hWork : plan.work ≤ P) :
    planFoot S plan ≤ planBound S A plan.sizes.sum P := by
  have hCount := GeneralPaperMeasuredPlanPositive.block_count plan hPos
  have hSizes := list_bound S (A + 1) natBits plan.sizes (by
    intro size hs
    have hSize := List.single_le_sum (fun x _ => Nat.zero_le x) size hs
    have hWidth := binaryWordWidth_le_of_lt_pow hA (hSize.trans_lt hCap)
    unfold natBits
    omega)
  have hPrice := Nat.add_le_add_left (binaryWordWidth_mono hWork) 1
  have hBlocks := Nat.mul_le_mul_right (A + 1 + 2 * S) hCount
  unfold planFoot planBound fields
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil]
  change natBits plan.work ≤ natBits P at hPrice
  nlinarith only [hSizes,hBlocks,hPrice]

def regionsFoot {A : ℕ} (S : ℕ) (regions : List (Region A)) : ℕ :=
  listFootprint S (regionFoot S) regions

def regionsBound (S A B : ℕ) : ℕ := B * (regionBound S A + 2 * S) + 32 * S

theorem regions_bound (model : RationalCostModel) (S A start : ℕ) (plan : Plan)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A)
    (hCap : start + plan.sizes.sum < 2 ^ A) :
    regionsFoot S (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 ≤
      regionsBound S A plan.sizes.sum := by
  have hRegions := GeneralPaperMeasuredBlockLayout.range model S A start plan
  have hList := list_bound S (regionBound S A) (regionFoot S)
    (GeneralPaperMeasuredBlockLayout.run model S A start plan).1 (by
      intro region hr
      exact region_bound S A region hA ((hRegions region hr).2.trans_lt hCap))
  rw [GeneralPaperMeasuredBlockLayout.count] at hList
  have hCount := GeneralPaperMeasuredPlanPositive.block_count plan hPos
  exact hList.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hCount) _)

theorem subregions_bound (model : RationalCostModel) (S A start : ℕ) (plan : Plan)
    (regions : List (Region A))
    (hFrom : regions.Sublist (GeneralPaperMeasuredBlockLayout.run model S A start plan).1)
    (hPos : GeneralPaperMeasuredPlanPositive.Positive plan) (hA : 0 < A)
    (hCap : start + plan.sizes.sum < 2 ^ A) :
    regionsFoot S regions ≤ regionsBound S A plan.sizes.sum := by
  have hRegions := GeneralPaperMeasuredBlockLayout.range model S A start plan
  have hList := list_bound S (regionBound S A) (regionFoot S) regions (by
    intro region hr
    exact region_bound S A region hA ((hRegions region (hFrom.subset hr)).2.trans_lt hCap))
  have hCount := hFrom.length_le
  rw [GeneralPaperMeasuredBlockLayout.count] at hCount
  have hBlocks := GeneralPaperMeasuredPlanPositive.block_count plan hPos
  exact hList.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (hCount.trans hBlocks)) _)

def twoPoolFoot (model : RationalCostModel) (S I A : ℕ) (inner outer : Plan) : ℕ :=
  let layout := GeneralPaperMeasuredTwoPoolLayout.run model S I A inner outer
  planFoot S inner + planFoot S outer + regionsFoot S layout.inner + regionsFoot S layout.outer +
    fields S [layout.boundary,layout.finish,layout.work] + 64 * S

def twoPoolBound (S I A Bi Bo Pi Po P : ℕ) : ℕ :=
  planBound S I Bi Pi + planBound S A Bo Po + regionsBound S I Bi + regionsBound S A Bo +
    2 * (A + 1) + natBits P + 99 * S

theorem two_pool_bound (model : RationalCostModel) (S I A : ℕ) (inner outer : Plan)
    (hInner : GeneralPaperMeasuredPlanPositive.Positive inner)
    (hOuter : GeneralPaperMeasuredPlanPositive.Positive outer) (hI : 0 < I) (hA : 0 < A)
    (hInnerCap : inner.sizes.sum < 2 ^ I) (hTotalCap : inner.sizes.sum + outer.sizes.sum < 2 ^ A)
    (Pi Po P : ℕ) (hPi : inner.work ≤ Pi) (hPo : outer.work ≤ Po)
    (hP : (GeneralPaperMeasuredTwoPoolLayout.run model S I A inner outer).work ≤ P) :
    twoPoolFoot model S I A inner outer ≤
      twoPoolBound S I A inner.sizes.sum outer.sizes.sum Pi Po P := by
  have hiPlan := plan_bound S I inner hInner hI hInnerCap Pi hPi
  have hoPlan := plan_bound S A outer hOuter hA (show outer.sizes.sum < 2 ^ A by omega) Po hPo
  have hiRegions := regions_bound model S I 0 inner hInner hI (by omega)
  have hoRegions := regions_bound model S A inner.sizes.sum outer hOuter hA hTotalCap
  have hBoundary := binaryWordWidth_le_of_lt_pow hA (show inner.sizes.sum < 2 ^ A by omega)
  have hFinish := binaryWordWidth_le_of_lt_pow hA hTotalCap
  have hPrice := Nat.add_le_add_left (binaryWordWidth_mono hP) 1
  have hoCursor := GeneralPaperMeasuredBlockLayout.cursor model S I 0 inner
  simp only [Nat.zero_add] at hoCursor
  have hiRegions' : regionsFoot S (GeneralPaperMeasuredTwoPoolLayout.run model S I A inner outer).inner ≤
      regionsBound S I inner.sizes.sum := hiRegions
  have hoRegions' : regionsFoot S (GeneralPaperMeasuredTwoPoolLayout.run model S I A inner outer).outer ≤
      regionsBound S A outer.sizes.sum := by
    simpa only [GeneralPaperMeasuredTwoPoolLayout.run,hoCursor] using hoRegions
  have hFields : fields S [(GeneralPaperMeasuredTwoPoolLayout.run model S I A inner outer).boundary,
      (GeneralPaperMeasuredTwoPoolLayout.run model S I A inner outer).finish,
      (GeneralPaperMeasuredTwoPoolLayout.run model S I A inner outer).work] ≤
      2 * (A + 1) + natBits P + 35 * S := by
    unfold fields natBits
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,
      GeneralPaperMeasuredTwoPoolLayout.boundary,GeneralPaperMeasuredTwoPoolLayout.finish]
    omega
  dsimp only [twoPoolFoot,twoPoolBound]
  omega

end Blotto.GeneralPaperMeasuredLayoutStorage
