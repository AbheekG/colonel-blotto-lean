import Blotto.GeneralPaperPricedRaySearch

/-! One priced crossing refinement: build one batch array, search it with
on-demand queries, and return the same adjacent bracket as the selected ray
routine. Query arithmetic/bit costs are supplied by that routine's DP price;
the array read, midpoint, index/control and return costs are included here.
-/
namespace Blotto.GeneralPaperPricedCrossingRefinement
open GeneralPaperRayCrossingRefinement
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Result where
  bracket : Option Bracket
  work : ℕ
  probes : ℕ

def readQuery {n : ℕ} (query : ℚ → Bool × ℕ) (W : ℕ) (values : FixedArrayTable n ℚ)
    (i : Fin n) : Bool × ℕ :=
  let current := query (values.read i)
  (current.1,current.2+8*W)

def run (primitive indexPrimitive : ℕ → ℕ) (W : ℕ) (query : ℚ → Bool × ℕ)
    (lo hi : ℚ) (points : List ℚ) : Result :=
  let values := GeneralPaperPricedCrossingArray.run primitive indexPrimitive W lo hi points
  let result := GeneralPaperPricedRaySearch.selected (readQuery query W values.1) W
  let bracket := if hr : 0<result.rank ∧ result.rank<(GeneralPaperRaySortedCrossings.ordered lo hi points).length then
    some (⟨values.1.read ⟨result.rank-1,by omega⟩,values.1.read ⟨result.rank,hr.2⟩⟩ : Bracket)
    else none
  ⟨bracket,values.2+result.work+24*W,result.probes⟩

theorem data (primitive indexPrimitive : ℕ → ℕ) (W : ℕ) (query : ℚ → Bool × ℕ)
    (lo hi : ℚ) (points : List ℚ) :
    (run primitive indexPrimitive W query lo hi points).bracket=narrow query lo hi points := by
  unfold run narrow
  simp only [GeneralPaperPricedCrossingArray.data]
  have he := GeneralPaperPricedRaySearch.selected_rank_congr
    (readQuery query W (GeneralPaperRaySortedCrossings.array lo hi points))
    (fun i => query ((GeneralPaperRaySortedCrossings.array lo hi points).read i)) (fun _ => rfl) W
  simp only [he]

theorem probes (primitive indexPrimitive : ℕ → ℕ) (W : ℕ) (query : ℚ → Bool × ℕ)
    (lo hi : ℚ) (points : List ℚ) :
    (run primitive indexPrimitive W query lo hi points).probes≤binaryWordWidth (points.length+3)+1 := by
  apply (GeneralPaperPricedRaySearch.selected_probes _ W).trans
  have hn := GeneralPaperRaySortedCrossings.ordered_length lo hi points
  exact Nat.add_le_add_right (binaryWordWidth_mono (by omega :
    (GeneralPaperRaySortedCrossings.ordered lo hi points).length≤points.length+3)) 1

def searchProfile (n W E : ℕ) : ℕ :=
  (binaryWordWidth (n+3)+1)*((12*(binaryWordWidth (n+3)+1)+42)*W+E)+
    (12*binaryWordWidth (n+3)+50)*W

theorem search_work (primitive indexPrimitive : ℕ → ℕ) (W E : ℕ)
    (query : ℚ → Bool × ℕ) (lo hi : ℚ) (points : List ℚ)
    (hQuery : ∀ q∈GeneralPaperRaySortedCrossings.ordered lo hi points,(query q).2≤E) :
    (run primitive indexPrimitive W query lo hi points).work≤
      (GeneralPaperPricedCrossingArray.run primitive indexPrimitive W lo hi points).2+
        searchProfile points.length W E := by
  let values := (GeneralPaperPricedCrossingArray.run primitive indexPrimitive W lo hi points).1
  have hEach (i) : (readQuery query W values i).2≤E+8*W := by
    have hm : values.read i∈GeneralPaperRaySortedCrossings.ordered lo hi points := by
      simp only [values,GeneralPaperPricedCrossingArray.data]
      exact GeneralPaperRaySortedCrossings.read_mem lo hi points i
    exact Nat.add_le_add_right (hQuery _ hm) _
  have hs := GeneralPaperPricedRaySearch.selected_work (readQuery query W values) W (E+8*W) hEach
  have hn := GeneralPaperRaySortedCrossings.ordered_length lo hi points
  have hw := binaryWordWidth_mono (by omega :
    (GeneralPaperRaySortedCrossings.ordered lo hi points).length≤points.length+3)
  have hd := (GeneralPaperRaySearchControls.depth_bound
    (GeneralPaperRaySortedCrossings.ordered lo hi points).length).trans (Nat.add_le_add_right hw 1)
  have hFactor : (12*GeneralPaperRaySearchControls.depth
      (GeneralPaperRaySortedCrossings.ordered lo hi points).length+34)*W+(E+8*W)≤
        (12*(binaryWordWidth (points.length+3)+1)+42)*W+E := by nlinarith only [hd]
  have hm := Nat.mul_le_mul hd hFactor
  have hc := Nat.mul_le_mul_right W (Nat.add_le_add_right (Nat.mul_le_mul_left 12 hw) 26)
  change _+(GeneralPaperPricedRaySearch.selected (readQuery query W values) W).work+24*W≤_
  unfold searchProfile
  nlinarith only [hs,hm,hc]

def profile (n W P E : ℕ) : ℕ :=
  GeneralPaperPricedCrossingArray.profile n W P+searchProfile n W E

theorem bit_work (model : RationalCostModel) (W R E : ℕ) (query : ℚ → Bool × ℕ)
    (lo hi : ℚ) (points : List ℚ) (hW : 1≤W) (hIndex : binaryWordWidth (points.length+3)≤W)
    (hl : RationalHeight lo R) (hh : RationalHeight hi R) (hp : ∀ q∈points,RationalHeight q R)
    (hQuery : ∀ q∈GeneralPaperRaySortedCrossings.ordered lo hi points,(query q).2≤E) :
    (run model.rat (fun w => w) W query lo hi points).work≤
      profile points.length W (model.rat (1+2*R)) E := by
  exact (search_work _ _ W E query lo hi points hQuery).trans
    (Nat.add_le_add_right
      (GeneralPaperPricedCrossingArray.bit_work model W R lo hi points hW hIndex hl hh hp) _)

theorem arithmetic_work (R E : ℕ) (query : ℚ → Bool × ℕ) (lo hi : ℚ) (points : List ℚ)
    (hl : RationalHeight lo R) (hh : RationalHeight hi R) (hp : ∀ q∈points,RationalHeight q R)
    (hQuery : ∀ q∈GeneralPaperRaySortedCrossings.ordered lo hi points,(query q).2≤E) :
    (run (fun _ => 1) (fun _ => 1) 1 query lo hi points).work≤profile points.length 1 1 E := by
  exact (search_work _ _ 1 E query lo hi points hQuery).trans
    (Nat.add_le_add_right (GeneralPaperPricedCrossingArray.arithmetic_work R lo hi points hl hh hp) _)

end Blotto.GeneralPaperPricedCrossingRefinement
