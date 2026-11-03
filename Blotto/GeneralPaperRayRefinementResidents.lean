import Blotto.GeneralPaperSourceSharpOwnerRates

/-! Residents after native crossing preparation: the input batch, returned
sorted/unique list, materialized array, endpoints and actual return metadata.
The payload is conservatively counted in both lists and the array. Internal
filter/sort/materialization and search-frame windows are separate phases. -/
namespace Blotto.GeneralPaperRayRefinementResidents
open GeneralPaperEncodedScalarStorage GeneralPaperRayUniformSize
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 8192

def listProfile (W n R : ℕ) : ℕ := n*(1+2*R+2*W)+32*W
def arrayProfile (W n R : ℕ) : ℕ := n*(1+2*R+W)+64*W

theorem price_mono {n q : ℕ} (hn : n≤q) (W P : ℕ) :
    GeneralPaperPricedCrossingArray.profile n W P≤GeneralPaperPricedCrossingArray.profile q W P := by
  have hs := GeneralPaperPricedSort.profile_mono (Nat.add_le_add_right hn 2) (W:=W) (P:=P)
  have hc := Nat.mul_le_mul_left (3*P+32*W) (Nat.add_le_add_right hn 2)
  have ha := Nat.mul_le_mul_right W (Nat.mul_le_mul_left 64 (Nat.add_le_add_right hn 3))
  unfold GeneralPaperPricedCrossingArray.profile GeneralPaperPricedCrossingSort.profile
  omega

def window (model : RationalCostModel) (W : ℕ) (lo hi : ℚ) (points : List ℚ) : ℕ :=
  let sorted := GeneralPaperPricedCrossingSort.run model.rat W lo hi points
  let materialized := PaperListReferenceArray.run (fun w => w) W sorted.1
  let result := GeneralPaperPricedCrossingArray.run model.rat (fun w => w) W lo hi points
  listFootprint W rationalWordWidth points+listFootprint W rationalWordWidth sorted.1+
    GeneralPaperEncodedRationalRows.rowFootprint W result.1+rationalWordWidth lo+rationalWordWidth hi+
    fields W [points.length,sorted.1.length,sorted.2,materialized.2,result.2,sorted.2+materialized.2]+256*W

def metadataCap (model : RationalCostModel) (W n R : ℕ) : ℕ :=
  n+3+GeneralPaperPricedCrossingArray.profile n W (model.rat (1+2*R))

def profile (model : RationalCostModel) (W n R : ℕ) : ℕ :=
  listProfile W n R+listProfile W (n+2) R+arrayProfile W (n+2) R+2*(1+2*R)+
    6*(natBits (metadataCap model W n R)+W)+32*W+256*W

theorem bounded (model : RationalCostModel) (W n R : ℕ) (lo hi : ℚ) (points : List ℚ)
    (hLen : points.length≤n) (hl : RationalHeight lo R) (hh : RationalHeight hi R)
    (hp : ∀ t∈points,RationalHeight t R) (hW : 1≤W) (hIndex : binaryWordWidth (points.length+3)≤W) :
    window model W lo hi points≤profile model W n R := by
  let sorted := GeneralPaperPricedCrossingSort.run model.rat W lo hi points
  let materialized := PaperListReferenceArray.run (fun w => w) W sorted.1
  let result := GeneralPaperPricedCrossingArray.run model.rat (fun w => w) W lo hi points
  have hRaw := list_bound W (1+2*R) rationalWordWidth points (fun t ht => rationalWordWidth_of_height (hp t ht))
  have hRaw' : listFootprint W rationalWordWidth points≤listProfile W n R :=
    hRaw.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hLen) _)
  have hSortedLen : sorted.1.length≤n+2 :=
    (GeneralPaperPricedCrossingSort.length model.rat W lo hi points).trans (Nat.add_le_add_right hLen 2)
  have hSorted := list_bound W (1+2*R) rationalWordWidth sorted.1
    (GeneralPaperPricedCrossingSort.width model.rat W (1+2*R) lo hi points
      (rationalWordWidth_of_height hl) (rationalWordWidth_of_height hh) (fun t ht => rationalWordWidth_of_height (hp t ht)))
  have hSorted' : listFootprint W rationalWordWidth sorted.1≤listProfile W (n+2) R :=
    hSorted.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hSortedLen) _)
  have hArray := GeneralPaperEncodedRationalRows.row_bound W R result.1 (by
    intro i
    dsimp only [result]
    rw [GeneralPaperPricedCrossingArray.data]
    exact GeneralPaperRayBracketSize.read_height lo hi points R hl hh hp i)
  have hArrayLen : (GeneralPaperRaySortedCrossings.ordered lo hi points).length≤n+2 :=
    (GeneralPaperRaySortedCrossings.ordered_length lo hi points).trans (Nat.add_le_add_right hLen 2)
  have hArray' : GeneralPaperEncodedRationalRows.rowFootprint W result.1≤arrayProfile W (n+2) R :=
    hArray.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hArrayLen) _)
  have hLo := rationalWordWidth_of_height hl
  have hHi := rationalWordWidth_of_height hh
  have hWork := (GeneralPaperPricedCrossingArray.bit_work model W R lo hi points hW hIndex hl hh hp).trans
    (price_mono hLen W (model.rat (1+2*R)))
  change result.2≤GeneralPaperPricedCrossingArray.profile n W (model.rat (1+2*R)) at hWork
  have hShape : result.2=sorted.2+materialized.2+8*W := rfl
  have hf := fields_bound W (natBits (metadataCap model W n R))
    [points.length,sorted.1.length,sorted.2,materialized.2,result.2,sorted.2+materialized.2] (by
      intro x hx
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold metadataCap; omega)
  change GeneralPaperEncodedScalarStorage.fields W _≤6*(natBits (metadataCap model W n R)+W)+32*W at hf
  change listFootprint W rationalWordWidth points+listFootprint W rationalWordWidth sorted.1+
    GeneralPaperEncodedRationalRows.rowFootprint W result.1+rationalWordWidth lo+rationalWordWidth hi+
    fields W [points.length,sorted.1.length,sorted.2,materialized.2,result.2,sorted.2+materialized.2]+256*W≤_
  unfold profile
  omega

theorem height_mono (model : RationalCostModel) (W n : ℕ) {R Q : ℕ} (h : R≤Q) :
    profile model W n R≤profile model W n Q := by
  unfold profile listProfile arrayProfile metadataCap GeneralPaperPricedCrossingArray.profile
    GeneralPaperPricedCrossingSort.profile GeneralPaperPricedSort.profile natBits
  gcongr <;> exact model.monotone (by omega)

theorem stage_batch {S K m : ℕ} (model : RationalCostModel) (W D E X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n+1≤m)
    (field : GeneralPaperRayAffineScoreStep.Field K) (previous : GeneralPaperRayAffineScoreStep.Table S K)
    (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field) (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous)
    (lo hi : ℚ) (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P))
    (hW : 1≤W) (hIndex : binaryWordWidth ((S+1)*(K*K)+3)≤W) :
    window model W lo hi (GeneralPaperNativeAffinePrices.crossingsRun model.rat W field previous).1≤
      profile model W ((S+1)*(K*K)) (width D E m X V P) := by
  have hLen : (GeneralPaperNativeAffinePrices.crossingsRun model.rat W field previous).1.length≤(S+1)*(K*K) := by
    rw [GeneralPaperNativeAffinePrices.crossings_data]
    exact GeneralPaperRayAffineScoreStep.crossings_length field previous
  apply bounded model W _ _ lo hi _ hLen hl hh _ hW ((binaryWordWidth_mono (Nat.add_le_add_right hLen 3)).trans hIndex)
  intro q hq
  rw [GeneralPaperNativeAffinePrices.crossings_data] at hq
  exact GeneralPaperRayUniformSize.stage_roots hD hE hn field previous hf hp q hq

theorem budget_batch {S K m : ℕ} (model : RationalCostModel) (W D E X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n≤m)
    (table : GeneralPaperRayAffineScoreStep.Table S K) (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n table)
    (h : ℕ) (beta : ℚ) (hb : GeneralPaperRayRationalBound.Bounded D P beta) (lo hi : ℚ)
    (hl : RationalHeight lo (width D E m X V P)) (hh : RationalHeight hi (width D E m X V P))
    (hW : 1≤W) (hIndex : binaryWordWidth (S+4)≤W) :
    window model W lo hi (GeneralPaperBudgetCrossingPrice.run model.rat W table h beta).1≤
      profile model W (S+1) (width D E m X V P) := by
  have hLen : (GeneralPaperBudgetCrossingPrice.run model.rat W table h beta).1.length≤S+1 := by
    rw [GeneralPaperBudgetCrossingPrice.data]
    exact GeneralPaperRayBudgetCrossings.batch_length table h beta
  apply bounded model W _ _ lo hi _ hLen hl hh _ hW ((binaryWordWidth_mono (Nat.add_le_add_right hLen 3)).trans hIndex)
  intro q hq
  rw [GeneralPaperBudgetCrossingPrice.data] at hq
  exact GeneralPaperRayUniformSize.budget_roots hD hE hn table hp h beta hb q hq

end Blotto.GeneralPaperRayRefinementResidents
