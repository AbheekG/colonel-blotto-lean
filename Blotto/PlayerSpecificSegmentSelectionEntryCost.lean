import Blotto.PlayerSpecificSegmentSelectionEntrySizes

/-! Complete segment-choice entry work is polynomial in the original
weight/root height, slot count and actual fair-bit precision. -/
namespace Blotto.PlayerSpecificSegmentSelectionEntryCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := (200001000*PlayerSpecificResourceCostProfile.rationalCoefficient+PlayerSpecificSegmentSelectionSizes.nodeCoefficient)*
  PlayerSpecificSegmentSelectionEntrySizes.coefficient^3+PlayerSpecificResourceBlockPolynomial.coefficient

theorem block_transfer (slots T H : ℕ) : PlayerSpecificResourceBlockPolynomial.coefficient*(slots-1+1)^3*(H+1)^3≤
    PlayerSpecificResourceBlockPolynomial.coefficient*(slots+1)^5*(T+H+1)^3 := by
  have hs : (slots-1+1)^3≤(slots+1)^5 := (Nat.pow_le_pow_left (show slots-1+1≤slots+1 by omega) 3).trans
    (Nat.pow_le_pow_right (by omega) (by decide : 3≤5))
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hs) (Nat.pow_le_pow_left (by omega : H+1≤T+H+1) 3)

theorem cost {N slots : ℕ} (root : Candidate) (d : Descriptor N slots) (fallback : Fin slots) (T H : ℕ)
    (bits : Fin ((slots-1)*H) → Bool) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hml : root.polynomial.length≤4) (hmT : HasHeight root.polynomial T) (he : HasHeight [root.interval.lo,root.interval.hi] T)
    (hv : root.interval.lo<root.interval.hi) (hT : 1≤T)
    (hw : ∀ j,Reduced root.polynomial (d.weights.read j) ∧ HasHeight (d.weights.read j) T) :
    (PlayerSpecificSegmentSelectionEntryExecution.run RationalCostModel.schoolbook root d fallback H bits).2≤
      coefficient*(slots+1)^5*(T+H+1)^3 := by
  let model:=RationalCostModel.schoolbook
  let S:=PlayerSpecificSegmentSelectionEntrySizes.massSize slots T
  let U:=PlayerSpecificSegmentSelectionSizes.size S H slots
  let B:=PlayerSpecificSegmentSelectionEntrySizes.coefficient
  let R:=PlayerSpecificResourceCostProfile.rationalCoefficient
  let A:=T+H+1
  let initial:=PlayerSpecificFieldCombinationContract.constant root.polynomial 1
  let blocks:=PlayerSpecificResourceBlockExecution.blocks model (slots-1) H bits
  let items:=(List.finRange slots).take (slots-1)
  let result:=PlayerSpecificSegmentSelectionExecution.select model root d.weights fallback H items initial.1 blocks.1
  have hmass:=PlayerSpecificSegmentSelectionEntrySizes.lower slots T
  have hlow:=PlayerSpecificSegmentSelectionSizes.lower S H slots
  have hTS : T≤S := hmass.1
  have hsize : U+1≤B*(slots+1)*A := PlayerSpecificSegmentSelectionEntrySizes.size_bound slots T H
  have hinitial : Reduced root.polynomial initial.1 := by
    rw [PlayerSpecificFieldCombinationContract.constant_value]
    exact PlayerSpecificAlgebraicField.constant_reduced _ _ hm hm0
  have hinitH : HasHeight initial.1 (PlayerSpecificAlgebraicHeightEnvelope.step T) := by
    rw [PlayerSpecificFieldCombinationContract.constant_value]
    exact PlayerSpecificAlgebraicHeightEnvelope.constant_height _ 1 T hmT (one_height.mono hT) hT hml
  have hinitS : HasHeight initial.1 S := mono hinitH (by have h:=hmass.2.2; omega)
  have hstart:=(PlayerSpecificAlgebraicInitialPrimitiveCost.constant_cost model root.polynomial 1 T hm hm0 hml hmT (one_height.mono hT) hT).trans
    (Nat.mul_le_mul_left _ (model.monotone ((PlayerSpecificAlgebraicExpressionPrimitiveCost.initial_width T).trans
      (PlayerSpecificSegmentSelectionSizes.width_mono (hTS.trans hlow.1)))))
  have hstartQ : price model initial.2≤((200000000*R)*B^3)*(slots+1)^5*A^3 :=
    (hstart.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial 200000000 U)).trans
      (PlayerSpecificSegmentSelectionEntrySizes.constant_transfer 200000000 R B slots A U hsize)
  have hblocksQ : blocks.2≤PlayerSpecificResourceBlockPolynomial.coefficient*(slots+1)^5*A^3 :=
    (PlayerSpecificResourceBlockPolynomial.cost (slots-1) H bits).trans (block_transfer slots T H)
  have hi0 : items.length≤slots-1 := List.length_take_le _ _
  have hi : items.length≤slots := hi0.trans (by omega)
  have hpot : PlayerSpecificAlgebraicHeightEnvelope.step T+(items.length+1)*(T+1)≤S :=
    (Nat.add_le_add_left (Nat.mul_le_mul_right (T+1) (Nat.add_le_add_right hi 1)) _).trans hmass.2.2
  have hblockLen : blocks.1.length=slots-1 := PlayerSpecificResourceBlockExecution.blocks_length model (slots-1) H bits
  have hloop:=PlayerSpecificSegmentSelectionSourceCost.cost root d.weights fallback H T S hm hm0 hml (mono hmT hTS) (mono he hTS) hv hmass.2.1 hTS hw
    items initial.1 (PlayerSpecificAlgebraicHeightEnvelope.step T) blocks.1 hinitial hinitH hpot hi (by rw [hblockLen]; omega)
  have hloop':=hloop.trans (Nat.mul_le_mul_right (PlayerSpecificSegmentSelectionSizes.work S H slots) (Nat.add_le_add_right hi 1))
  have hloopQ : result.2≤(PlayerSpecificSegmentSelectionSizes.nodeCoefficient*B^3)*(slots+1)^5*A^3 :=
    hloop'.trans (PlayerSpecificSegmentSelectionEntrySizes.loop_transfer _ B slots A U hsize)
  have hvisits : result.1.2≤slots := (PlayerSpecificSegmentSelectionExecution.visits model root d.weights fallback H items initial.1 blocks.1).trans hi
  have hf:=PlayerSpecificSegmentSelectionFramePolynomial.cost root d.weights fallback H items initial.1 [] [] blocks.1.length result.1 S
    (mono hmT hTS) hml (mono he hTS) (fun j => ⟨(hw j).1,mono (hw j).2 hTS⟩) ⟨hinitial,hinitS⟩
    ⟨nil_reduced _ hm0,nil_height _⟩ ⟨nil_reduced _ hm0,nil_height _⟩ hi (by rw [hblockLen]; omega) hvisits
  have hfQ:=hf.trans (PlayerSpecificSegmentSelectionEntrySizes.frame_transfer 1000 R B slots A U hsize)
  have hsum:=Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hstartQ hblocksQ) hloopQ) hfQ
  change price model initial.2+blocks.2+result.2+
    price model (PlayerSpecificSegmentSelectionExecution.frame root d.weights fallback H items initial.1 [] [] blocks.1.length result.1)≤_
  apply hsum.trans_eq
  change _=((200001000*R+PlayerSpecificSegmentSelectionSizes.nodeCoefficient)*B^3+PlayerSpecificResourceBlockPolynomial.coefficient)*(slots+1)^5*A^3
  ring

theorem same_return_and_cost {N slots : ℕ} (root : Candidate) (d : Descriptor N slots) (fallback : Fin slots) (T H : ℕ)
    (bits : Fin ((slots-1)*H) → Bool) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hml : root.polynomial.length≤4) (hmT : HasHeight root.polynomial T) (he : HasHeight [root.interval.lo,root.interval.hi] T)
    (hv : root.interval.lo<root.interval.hi) (hT : 1≤T)
    (hw : ∀ j,Reduced root.polynomial (d.weights.read j) ∧ HasHeight (d.weights.read j) T) :
    (PlayerSpecificSegmentSelectionEntryExecution.run RationalCostModel.schoolbook root d fallback H bits).1=
      PlayerSpecificAlgebraicSegmentSample.selected RationalCostModel.schoolbook root d fallback H bits ∧
    (PlayerSpecificSegmentSelectionEntryExecution.run RationalCostModel.schoolbook root d fallback H bits).2≤coefficient*(slots+1)^5*(T+H+1)^3 :=
  ⟨PlayerSpecificSegmentSelectionEntryExecution.value _ root d fallback H bits,cost root d fallback T H bits hm hm0 hml hmT he hv hT hw⟩

end Blotto.PlayerSpecificSegmentSelectionEntryCost
