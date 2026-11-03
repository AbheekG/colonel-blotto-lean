import Blotto.PlayerSpecificSegmentDrawFramePolynomial

/-! The complete actual finite segment draw has one original-input
polynomial source contract: addressed packets, choice, midpoint,
interpolation and the retained descriptor/returned allocation all join. -/
namespace Blotto.PlayerSpecificSegmentDrawSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment PlayerSpecificAlgebraicDescriptorBounds
open PlayerSpecificSegmentDrawSizes
set_option autoImplicit false
set_option maxHeartbeats 2500000

def localCoefficient : ℕ := PlayerSpecificSegmentDrawPacketCost.coefficient+PlayerSpecificBitSlicePolynomial.coefficient+
  PlayerSpecificBitSlicePolynomial.coefficient+PlayerSpecificSegmentSelectionEntryCost.coefficient+2000*(192*192+192)+
  PlayerSpecificSegmentInterpolationSourceCost.coefficient*7^3+PlayerSpecificSegmentDrawFramePolynomial.coefficient
def coefficient : ℕ := localCoefficient*24^8

theorem cost {N slots : ℕ} (root : Candidate) (d : Descriptor N slots) (fallback : Fin slots) (T H K : ℕ)
    (bits : Fin ((slots-1)*H+K) → Bool) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hml : root.polynomial.length≤4) (hmT : HasHeight root.polynomial T) (he : HasHeight [root.interval.lo,root.interval.hi] T)
    (hv : root.interval.lo<root.interval.hi) (hT : 1≤T) (hd : Bounds root d T) :
    (PlayerSpecificSegmentDrawExecution.run RationalCostModel.schoolbook root d fallback H K bits).2≤
      coefficient*(T+N+slots+H+K+1)^16 := by
  let model:=RationalCostModel.schoolbook
  let S:=size N slots T H K
  let R:=(slots-1)*H
  let M:=R+K
  let headBits:=PlayerSpecificNaturalExecution.binary model (fun a b => a*b) (slots-1) H
  let count:=PlayerSpecificNaturalExecution.binary model (fun a b => a+b) R K
  let coins:=PlayerSpecificBitSliceExecution.run model M 0 R (by dsimp [M]; omega) bits
  let scalar:=PlayerSpecificBitSliceExecution.run model M R K (Nat.le_refl _) bits
  let choice:=PlayerSpecificSegmentSelectionEntryExecution.run model root d fallback H coins.1
  let midpoint:=PlayerSpecificMidpointExecution.run model K scalar.1
  let result:=PlayerSpecificSegmentInterpolationExecution.run model root d choice.1.1 midpoint.1
  have hS : 1≤S := by dsimp [S,size]; omega
  have hM : M+1≤S := by change packetCount slots H K+1≤S; dsimp [S,size]; omega
  have hslots : slots+1≤S := by dsimp [S,size]; omega
  have hH : T+H+1≤S := by dsimp [S,size]; omega
  have hK : K+1≤S := by dsimp [S,size]; omega
  have hN : N+1≤S := by dsimp [S,size]; omega
  have hcounts : headBits.2+count.2≤PlayerSpecificSegmentDrawPacketCost.coefficient*S^8 := PlayerSpecificSegmentDrawPacketCost.cost N slots T H K
  have hcoins : coins.2≤PlayerSpecificBitSlicePolynomial.coefficient*S^8 :=
    (PlayerSpecificBitSlicePolynomial.cost M 0 R (by dsimp [M]; omega) bits).trans
      (power_transfer _ (M+1) S 3 hM (by decide) hS)
  have hscalar : scalar.2≤PlayerSpecificBitSlicePolynomial.coefficient*S^8 :=
    (PlayerSpecificBitSlicePolynomial.cost M R K (Nat.le_refl _) bits).trans
      (power_transfer _ (M+1) S 3 hM (by decide) hS)
  have hchoice0:=PlayerSpecificSegmentSelectionEntryCost.cost root d fallback T H coins.1 hm hm0 hml hmT he hv hT hd.weights
  have hchoice : choice.2≤PlayerSpecificSegmentSelectionEntryCost.coefficient*S^8 :=
    hchoice0.trans (selection_transfer _ (slots+1) (T+H+1) S hslots hH)
  have hmidpoint : midpoint.2≤(2000*(192*192+192))*S^8 :=
    (PlayerSpecificMidpointCost.polynomial_cost K scalar.1).trans (power_transfer _ (K+1) S 3 hK (by decide) hS)
  let V:=T+2*K+6
  have hTV : T≤V := by dsimp [V]; omega
  have hq : RationalHeight midpoint.1 V := by
    rw [PlayerSpecificMidpointExecution.value]
    exact (dyadicMidpointSample_height K scalar.1).mono (by dsimp [V]; omega)
  have hinterp0:=PlayerSpecificSegmentInterpolationSourceCost.cost root d choice.1.1 midpoint.1 V hm hm0 hml
    (mono hmT hTV) (mono he hTV) hv hq (by dsimp [V]; omega)
    (fun j => ⟨(hd.first choice.1.1 j).1,mono (hd.first choice.1.1 j).2 hTV⟩)
    (fun j => ⟨(hd.second choice.1.1 j).1,mono (hd.second choice.1.1 j).2 hTV⟩)
  have hinterp4 : result.2≤(PlayerSpecificSegmentInterpolationSourceCost.coefficient*7^3)*S^4 :=
    hinterp0.trans (interpolation_transfer _ (N+1) (V+N+slots+1) S hN (by dsimp [V,S,size]; omega))
  have hinterp : result.2≤(PlayerSpecificSegmentInterpolationSourceCost.coefficient*7^3)*S^8 :=
    hinterp4.trans (power_transfer _ S S 4 (Nat.le_refl _) (by decide) hS)
  have hvisits : choice.1.2≤slots := by
    change (PlayerSpecificSegmentSelectionEntryExecution.run model root d fallback H coins.1).1.2≤slots
    rw [PlayerSpecificSegmentSelectionEntryExecution.value]
    exact (PlayerSpecificAlgebraicSegmentSample.selected_visits model root d fallback H coins.1).trans (by omega)
  have hframe:=PlayerSpecificSegmentDrawFramePolynomial.cost root d fallback choice.1 T H K bits hm hm0 hml hmT he hd hvisits
  have hsum:=Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hcounts hcoins) hscalar) hchoice) hmidpoint) hinterp) hframe
  have hlocal : (PlayerSpecificSegmentDrawExecution.run model root d fallback H K bits).2≤localCoefficient*S^8 := by
    apply hsum.trans_eq
    change _=(PlayerSpecificSegmentDrawPacketCost.coefficient+PlayerSpecificBitSlicePolynomial.coefficient+
      PlayerSpecificBitSlicePolynomial.coefficient+PlayerSpecificSegmentSelectionEntryCost.coefficient+2000*(192*192+192)+
      PlayerSpecificSegmentInterpolationSourceCost.coefficient*7^3+PlayerSpecificSegmentDrawFramePolynomial.coefficient)*S^8
    simp only [Nat.add_mul]
    rfl
  exact hlocal.trans (transfer localCoefficient N slots T H K)

theorem same_return_and_cost {N slots : ℕ} (root : Candidate) (d : Descriptor N slots) (fallback : Fin slots) (T H K : ℕ)
    (bits : Fin ((slots-1)*H+K) → Bool) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hml : root.polynomial.length≤4) (hmT : HasHeight root.polynomial T) (he : HasHeight [root.interval.lo,root.interval.hi] T)
    (hv : root.interval.lo<root.interval.hi) (hT : 1≤T) (hd : Bounds root d T) :
    (PlayerSpecificSegmentDrawExecution.run RationalCostModel.schoolbook root d fallback H K bits).1=
      PlayerSpecificAlgebraicSegmentSample.sample RationalCostModel.schoolbook root d fallback H K bits ∧
    (PlayerSpecificSegmentDrawExecution.run RationalCostModel.schoolbook root d fallback H K bits).2≤coefficient*(T+N+slots+H+K+1)^16 :=
  ⟨PlayerSpecificSegmentDrawExecution.value _ root d fallback H K bits,cost root d fallback T H K bits hm hm0 hml hmT he hv hT hd⟩

end Blotto.PlayerSpecificSegmentDrawSourceCost
