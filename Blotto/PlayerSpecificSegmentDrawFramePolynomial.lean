import Blotto.PlayerSpecificSegmentDrawReturnSizes

/-! Complete measured segment return frames have one polynomial source
bound using sizes derived from the original descriptor and precisions. -/
namespace Blotto.PlayerSpecificSegmentDrawFramePolynomial
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicSegment PlayerSpecificAlgebraicDescriptorBounds
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := (1000*PlayerSpecificResourceCostProfile.rationalCoefficient)*PlayerSpecificSegmentDrawSizes.heightCoefficient^3

theorem cost {N slots : ℕ} (root : Candidate) (d : Descriptor N slots) (fallback : Fin slots) (choice : Fin slots×ℕ) (T H K : ℕ)
    (bits : Fin ((slots-1)*H+K) → Bool) (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[])
    (hml : root.polynomial.length≤4) (hmT : HasHeight root.polynomial T) (he : HasHeight [root.interval.lo,root.interval.hi] T)
    (hd : Bounds root d T) (hvisits : choice.2≤slots) :
    price RationalCostModel.schoolbook (PlayerSpecificSegmentDrawExecution.frame root d H K
      (PlayerSpecificSegmentDrawSizes.headCount slots H) (PlayerSpecificSegmentDrawSizes.packetCount slots H K) choice
      (PlayerSpecificSegmentDrawExecution.run RationalCostModel.schoolbook root d fallback H K bits).1)≤
        coefficient*(PlayerSpecificSegmentDrawSizes.size N slots T H K)^8 := by
  let model:=RationalCostModel.schoolbook
  let U:=PlayerSpecificSegmentDrawSizes.height N slots T H K
  let S:=PlayerSpecificSegmentDrawSizes.size N slots T H K
  have hbase:=PlayerSpecificAlgebraicExpressionBudget.initial_le 3 (T+2*K+6)
  have hTU : T≤U := by dsimp [U,PlayerSpecificSegmentDrawSizes.height]; omega
  have hN : N≤U := by dsimp [U,PlayerSpecificSegmentDrawSizes.height]; omega
  have hslots : slots≤U := by dsimp [U,PlayerSpecificSegmentDrawSizes.height]; omega
  have hH : H≤U := by dsimp [U,PlayerSpecificSegmentDrawSizes.height]; omega
  have hK : K≤U := by dsimp [U,PlayerSpecificSegmentDrawSizes.height]; omega
  have hhead : PlayerSpecificSegmentDrawSizes.headCount slots H≤U := by dsimp [U,PlayerSpecificSegmentDrawSizes.height]; omega
  have hcount : PlayerSpecificSegmentDrawSizes.packetCount slots H K≤U := by dsimp [U,PlayerSpecificSegmentDrawSizes.height]; omega
  have hU : 1≤U := by dsimp [U,PlayerSpecificSegmentDrawSizes.height]; omega
  have hr:=PlayerSpecificSegmentDrawReturnSizes.output model root d fallback T H K bits hm hm0 hml hmT hd
  have hf:=PlayerSpecificSegmentDrawFrameCost.cost model root d H K (PlayerSpecificSegmentDrawSizes.headCount slots H)
    (PlayerSpecificSegmentDrawSizes.packetCount slots H K) choice (PlayerSpecificSegmentDrawExecution.run model root d fallback H K bits).1 U
    (mono hmT hTU) hml (mono he hTU) (PlayerSpecificSegmentDrawReturnSizes.bounds_mono root d T U hTU hd)
    (fun j => ⟨(hr j).2,by have h:=(hr j).1.2; omega⟩) hN hslots hH hK hhead hcount (hvisits.trans hslots) hU
  have hf':=hf.trans (PlayerSpecificSegmentSelectionSizes.rational_polynomial (1000*(N+1)*(slots+1)) U)
  have hNS : N+1≤S := by dsimp [S,PlayerSpecificSegmentDrawSizes.size]; omega
  have hslotsS : slots+1≤S := by dsimp [S,PlayerSpecificSegmentDrawSizes.size]; omega
  have hheight : U+1≤PlayerSpecificSegmentDrawSizes.heightCoefficient*S := PlayerSpecificSegmentDrawSizes.height_bound N slots T H K
  have hp:=hf'.trans (PlayerSpecificSegmentDrawSizes.frame_transfer 1000 PlayerSpecificResourceCostProfile.rationalCoefficient
    PlayerSpecificSegmentDrawSizes.heightCoefficient (N+1) (slots+1) (U+1) S hNS hslotsS hheight)
  have hS : 1≤S := by dsimp [S,PlayerSpecificSegmentDrawSizes.size]; omega
  exact hp.trans (PlayerSpecificSegmentDrawSizes.power_transfer coefficient S S 5 (Nat.le_refl _) (by decide) hS)

end Blotto.PlayerSpecificSegmentDrawFramePolynomial
