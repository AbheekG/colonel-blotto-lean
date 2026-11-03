import Blotto.GeneralPaperPricedCrossingSort
import Blotto.PaperListReferenceArray

/-! Materialize exactly the sorted crossing array, once, by a linear
reference-buffer traversal. Both comparison and index primitive prices are
explicit; the word-capacity premise belongs to the caller's control ledger.
-/
namespace Blotto.GeneralPaperPricedCrossingArray
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run (primitive indexPrimitive : ℕ → ℕ) (W : ℕ) (lo hi : ℚ) (points : List ℚ) :
    FixedArrayTable (GeneralPaperRaySortedCrossings.ordered lo hi points).length ℚ × ℕ :=
  let sorted := GeneralPaperPricedCrossingSort.run primitive W lo hi points
  let materialized := PaperListReferenceArray.run indexPrimitive W sorted.1
  (⟨materialized.1,by
      rw [PaperListReferenceArray.size,GeneralPaperPricedCrossingSort.data]⟩,
    sorted.2+materialized.2+8*W)

theorem data (primitive indexPrimitive : ℕ → ℕ) (W : ℕ) (lo hi : ℚ) (points : List ℚ) :
    (run primitive indexPrimitive W lo hi points).1=GeneralPaperRaySortedCrossings.array lo hi points := by
  unfold run GeneralPaperRaySortedCrossings.array
  simp only [PaperListReferenceArray.data,GeneralPaperPricedCrossingSort.data]

def profile (n W P : ℕ) : ℕ := GeneralPaperPricedCrossingSort.profile n W P+64*(n+3)*W+8*W

theorem bit_work (model : RationalCostModel) (W R : ℕ) (lo hi : ℚ) (points : List ℚ)
    (hW : 1≤W) (hIndex : binaryWordWidth (points.length+3)≤W)
    (hl : RationalHeight lo R) (hh : RationalHeight hi R) (hp : ∀ q∈points,RationalHeight q R) :
    (run model.rat (fun w => w) W lo hi points).2≤profile points.length W (model.rat (1+2*R)) := by
  let sorted := GeneralPaperPricedCrossingSort.run model.rat W lo hi points
  have hs := GeneralPaperPricedCrossingSort.bit_work model W R lo hi points hl hh hp
  change sorted.2≤_ at hs
  have hn : sorted.1.length≤points.length+2 := GeneralPaperPricedCrossingSort.length _ _ _ _ _
  have hi := (binaryWordWidth_mono (Nat.add_le_add_right hn 1)).trans hIndex
  have ha := PaperListReferenceArray.bit_work W sorted.1 hW hi
  have hm := Nat.mul_le_mul_right W (Nat.mul_le_mul_left 64 (Nat.add_le_add_right hn 1))
  have ha' : (PaperListReferenceArray.run (fun w => w) W sorted.1).2≤64*(points.length+3)*W := by
    apply ha.trans
    convert hm using 1
  change sorted.2+(PaperListReferenceArray.run (fun w => w) W sorted.1).2+8*W≤_
  unfold profile
  omega

theorem arithmetic_work (R : ℕ) (lo hi : ℚ) (points : List ℚ)
    (hl : RationalHeight lo R) (hh : RationalHeight hi R) (hp : ∀ q∈points,RationalHeight q R) :
    (run (fun _ => 1) (fun _ => 1) 1 lo hi points).2≤profile points.length 1 1 := by
  let sorted := GeneralPaperPricedCrossingSort.run (fun _ => 1) 1 lo hi points
  have hs := GeneralPaperPricedCrossingSort.arithmetic_work R lo hi points hl hh hp
  change sorted.2≤_ at hs
  have hn : sorted.1.length≤points.length+2 := GeneralPaperPricedCrossingSort.length _ _ _ _ _
  have ha := PaperListReferenceArray.arithmetic_work sorted.1
  change sorted.2+(PaperListReferenceArray.run (fun _ => 1) 1 sorted.1).2+8*1≤_
  unfold profile
  omega

end Blotto.GeneralPaperPricedCrossingArray
