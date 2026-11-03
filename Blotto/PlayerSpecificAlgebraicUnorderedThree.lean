import Blotto.PlayerSpecificAlgebraicOrderedThree

/-! A single exact comparison orders the first two algebraic lengths.
The swapped branch restores the original coordinate order in the cached
descriptor, including the exceptional boundary case. -/
namespace Blotto.PlayerSpecificAlgebraicUnorderedThree
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicThreeInput
open PlayerSpecificAlgebraicCandidates (Candidate)
open PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Values (a : Input) (i : ThreeSpec) (x : ℝ) : Prop where
  budget : realEvaluate a.budget x=i.B
  first : realEvaluate a.first x=i.a
  second : realEvaluate a.second x=i.d
  third : realEvaluate a.third x=i.c
  probability : realEvaluate a.probability x=i.p

def swapped (a : Input) : Input := ⟨a.budget,a.second,a.first,a.third,a.probability⟩

def permuted (d : Descriptor 3 9) : Descriptor 3 9 :=
  ⟨d.weights,
    FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn ![(d.first.read slot).read 1,(d.first.read slot).read 0,(d.first.read slot).read 2]),
    FixedArrayTable.ofFn (fun slot => FixedArrayTable.ofFn ![(d.second.read slot).read 1,(d.second.read slot).read 0,(d.second.read slot).read 2])⟩

def prepare (model : RationalCostModel) (root : Candidate) (a : Input) : Descriptor 3 9 :=
  if PlayerSpecificAlgebraicPairStep.le model root a.first a.second then PlayerSpecificAlgebraicOrderedThree.prepare model root a
  else permuted (PlayerSpecificAlgebraicOrderedThree.prepare model root (swapped a))

theorem fields (model : RationalCostModel) (root : Candidate) (a : Input) (i : ThreeSpec)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x) (ha : Values a i x) :
    (∀ slot,realEvaluate ((prepare model root a).weights.read slot) x=i.segmentLottery.weight slot) ∧
      (∀ slot j,realEvaluate (((prepare model root a).first.read slot).read j) x=i.segmentLottery.P slot j) ∧
      (∀ slot j,realEvaluate (((prepare model root a).second.read slot).read j) x=i.segmentLottery.Q slot j) := by
  have hc:=PlayerSpecificAlgebraicPairStep.le_correct model root a.first a.second hm hirr hv x hx
  rw [ha.first,ha.second] at hc
  by_cases hab : i.a≤ i.d
  · have hin : PlayerSpecificAlgebraicThreeInput.Values a i.orderedInput x := by
      refine ⟨ha.budget,?_,?_,ha.third,ha.probability⟩
      · simpa only [ThreeSpec.orderedInput,min_eq_left hab] using ha.first
      · simpa only [ThreeSpec.orderedInput,max_eq_right hab] using ha.second
    have hf:=PlayerSpecificAlgebraicOrderedThree.fields model root a i.orderedInput hm hirr hv x hx hin
    simpa only [prepare,ite_eq_left (hc.mpr hab),ThreeSpec.segmentLottery,ite_eq_left hab] using hf
  · have hba : i.d≤ i.a := (lt_of_not_ge hab).le
    have hin : PlayerSpecificAlgebraicThreeInput.Values (swapped a) i.orderedInput x := by
      refine ⟨ha.budget,?_,?_,ha.third,ha.probability⟩
      · simpa only [swapped,ThreeSpec.orderedInput,min_eq_right hba] using ha.second
      · simpa only [swapped,ThreeSpec.orderedInput,max_eq_left hba] using ha.first
    have hf:=PlayerSpecificAlgebraicOrderedThree.fields model root (swapped a) i.orderedInput hm hirr hv x hx hin
    rw [prepare,ite_eq_right (fun h => hab (hc.mp h))]
    refine ⟨?_,?_,?_⟩
    · intro slot
      simpa only [permuted,ThreeSpec.segmentLottery,ite_eq_right hab,SegmentLottery.mapped] using hf.1 slot
    · intro slot j
      fin_cases j <;> simp [permuted,FixedArrayTable.read_ofFn,ThreeSpec.segmentLottery,hab,
        SegmentLottery.mapped,AffineAllocation.swapFirst,swapFirst,hf.2.1]
    · intro slot j
      fin_cases j <;> simp [permuted,FixedArrayTable.read_ofFn,ThreeSpec.segmentLottery,hab,
        SegmentLottery.mapped,AffineAllocation.swapFirst,swapFirst,hf.2.2]

end Blotto.PlayerSpecificAlgebraicUnorderedThree
