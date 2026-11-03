import Blotto.PlayerSpecificSegmentInterpolationScalars

/-! Complete actual interpolation has polynomial source work from
original endpoints and rational scalar sizes. Scalar rows, coordinate
arrays and every retained/copy/index return are included. -/
namespace Blotto.PlayerSpecificSegmentInterpolationSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def localCoefficient : ℕ := 400001015*PlayerSpecificResourceCostProfile.rationalCoefficient+
  PlayerSpecificInterpolationCoordinateSourceCost.coefficient
def coefficient : ℕ := localCoefficient*PlayerSpecificSegmentInterpolationSizes.coefficient^3

theorem profile (R C N X : ℕ) : (400000015*R)*X+N*(C*X)+((1000*(N+1))*R)*X≤
    (400001015*R+C)*(N+1)*X := by
  nlinarith only [Nat.zero_le (N*R*X),Nat.zero_le (C*X)]

theorem cost {N slots : ℕ} (root : Candidate) (d : Descriptor N slots) (slot : Fin slots) (q : ℚ) (T : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (he : HasHeight [root.interval.lo,root.interval.hi] T)
    (hv : root.interval.lo<root.interval.hi) (hq : RationalHeight q T) (hT : 1≤T)
    (hp : ∀ j,Reduced root.polynomial ((d.first.read slot).read j) ∧ HasHeight ((d.first.read slot).read j) T)
    (hQ : ∀ j,Reduced root.polynomial ((d.second.read slot).read j) ∧ HasHeight ((d.second.read slot).read j) T) :
    (PlayerSpecificSegmentInterpolationExecution.run RationalCostModel.schoolbook root d slot q).2≤
      coefficient*(N+1)*(T+N+slots+1)^3 := by
  let model:=RationalCostModel.schoolbook
  let S:=PlayerSpecificSegmentInterpolationSizes.base T
  let V:=PlayerSpecificSegmentInterpolationSizes.scalarHeight T
  let U:=PlayerSpecificSegmentInterpolationSizes.height N slots T
  let X:=(U+16)^3
  let R:=PlayerSpecificResourceCostProfile.rationalCoefficient
  let C:=PlayerSpecificInterpolationCoordinateSourceCost.coefficient
  let complement:=scalar .subtract 1 q
  let left:=PlayerSpecificFieldCombinationContract.constant root.polynomial complement.1
  let right:=PlayerSpecificFieldCombinationContract.constant root.polynomial q
  let first:=d.first.read slot
  let second:=d.second.read slot
  let coordinates:=FixedArrayTable.ofFn (fun j => PlayerSpecificInterpolationCoordinateExecution.run model root left.1 right.1 (first.read j) (second.read j))
  let result:=(PlayerSpecificSegmentInterpolationExecution.run model root d slot q).1
  have hbase:=PlayerSpecificSegmentInterpolationSizes.base_lower T
  have hlow:=PlayerSpecificSegmentInterpolationSizes.lower N slots T
  have hTU : T≤U := hbase.1.trans hlow.1
  have hSV : S≤V := Nat.le_of_lt (PlayerSpecificAlgebraicHeightEnvelope.large S)
  have hTV : T≤V := hbase.1.trans hSV
  have hscalars:=PlayerSpecificSegmentInterpolationScalars.fits root q T hm hm0 hml hmT hq hT
  have hc : RationalHeight complement.1 S := hscalars.1
  have hl : Reduced root.polynomial left.1 ∧ HasHeight left.1 V := hscalars.2.1
  have hr : Reduced root.polynomial right.1 ∧ HasHeight right.1 V := hscalars.2.2
  have hsetup:=PlayerSpecificSegmentInterpolationScalars.setup_cost root q T N slots hm hm0 hml hmT hq hT
  have hcoordinate : ∀ j : Fin N,(coordinates.read j).2≤C*X := by
    intro j
    rw [FixedArrayTable.read_ofFn]
    have hj:=PlayerSpecificInterpolationCoordinateSourceCost.cost root left.1 right.1 (first.read j) (second.read j) V
      hm hm0 hml (mono hmT hTV) (mono he hTV) hv hl hr ⟨(hp j).1,mono (hp j).2 hTV⟩ ⟨(hQ j).1,mono (hQ j).2 hTV⟩
    exact hj.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.add_le_add_right hlow.2.1 16) 3))
  have hcoordinates : (∑ j : Fin N,(coordinates.read j).2)≤N*(C*X) := by
    have hs:=Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hcoordinate j)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using hs
  have hyH:=PlayerSpecificAlgebraicSegmentHeights.interpolation root d slot q hm hm0 hml S hbase.2 (mono hmT hbase.1)
    (hq.mono hbase.1) hc (fun j => ⟨(hp j).1,mono (hp j).2 hbase.1⟩) (fun j => ⟨(hQ j).1,mono (hQ j).2 hbase.1⟩)
  have hreturnU : PlayerSpecificAlgebraicHeightEnvelope.iterate 3 S≤U := by
    change PlayerSpecificAlgebraicHeightEnvelope.iterate 3 (PlayerSpecificSegmentInterpolationSizes.base T)≤
      PlayerSpecificAlgebraicHeightEnvelope.iterate 3 (PlayerSpecificSegmentInterpolationSizes.base T)+N+slots+10
    omega
  have hy : ∀ j,HasHeight (result.read j) U ∧ (result.read j).length≤3 := by
    intro j
    change HasHeight ((PlayerSpecificSegmentInterpolationExecution.run model root d slot q).1.read j) U ∧
      ((PlayerSpecificSegmentInterpolationExecution.run model root d slot q).1.read j).length≤3
    rw [PlayerSpecificSegmentInterpolationExecution.value]
    refine ⟨mono (hyH j) hreturnU,?_⟩
    have hred : Reduced root.polynomial ((PlayerSpecificAlgebraicSegment.interpolate root d slot q).read j) := by
      rw [PlayerSpecificAlgebraicSegment.interpolate,FixedArrayTable.read_ofFn]
      exact PlayerSpecificAlgebraicField.plus_reduced _ _ _ hm hm0
    have h:=hred.2
    omega
  have hf:=PlayerSpecificSegmentInterpolationFrameCost.cost model root first second result slot q complement.1 left.1 right.1 U
    (mono hmT hTU) hml (mono he hTU) (hq.mono hTU) (hc.mono hlow.1)
    ⟨mono hl.2 hlow.2.1,by have h:=hl.1.2; omega⟩ ⟨mono hr.2 hlow.2.1,by have h:=hr.1.2; omega⟩
    (fun j => ⟨mono (hp j).2 hTU,by change ((d.first.read slot).read j).length≤3; have h:=(hp j).1.2; omega⟩)
    (fun j => ⟨mono (hQ j).2 hTU,by change ((d.second.read slot).read j).length≤3; have h:=(hQ j).1.2; omega⟩) hy hlow.2.2.1 hlow.2.2.2.1 hlow.2.2.2.2
  have hf':=(hf.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial (1000*(N+1)) U)).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (show U+1≤U+16 by omega) 3))
  have hsum:=Nat.add_le_add (Nat.add_le_add hsetup hcoordinates) hf'
  have hlocal : (PlayerSpecificSegmentInterpolationExecution.run model root d slot q).2≤localCoefficient*(N+1)*X :=
    hsum.trans (profile R C N X)
  exact hlocal.trans (PlayerSpecificSegmentInterpolationSizes.transfer localCoefficient _ N slots T U
    (PlayerSpecificSegmentInterpolationSizes.linear N slots T))

theorem same_return_and_cost {N slots : ℕ} (root : Candidate) (d : Descriptor N slots) (slot : Fin slots) (q : ℚ) (T : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (he : HasHeight [root.interval.lo,root.interval.hi] T)
    (hv : root.interval.lo<root.interval.hi) (hq : RationalHeight q T) (hT : 1≤T)
    (hp : ∀ j,Reduced root.polynomial ((d.first.read slot).read j) ∧ HasHeight ((d.first.read slot).read j) T)
    (hQ : ∀ j,Reduced root.polynomial ((d.second.read slot).read j) ∧ HasHeight ((d.second.read slot).read j) T) :
    (PlayerSpecificSegmentInterpolationExecution.run RationalCostModel.schoolbook root d slot q).1=interpolate root d slot q ∧
    (PlayerSpecificSegmentInterpolationExecution.run RationalCostModel.schoolbook root d slot q).2≤coefficient*(N+1)*(T+N+slots+1)^3 :=
  ⟨PlayerSpecificSegmentInterpolationExecution.value _ root d slot q,cost root d slot q T hm hm0 hml hmT he hv hq hT hp hQ⟩

end Blotto.PlayerSpecificSegmentInterpolationSourceCost
