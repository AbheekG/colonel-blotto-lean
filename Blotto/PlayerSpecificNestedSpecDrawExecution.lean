import Blotto.PlayerSpecificNestedSpecProfileSourceCost

/-! Complete actual closed-probability nested draw: reserve and cache its bit
blocks once, prepare one reached profile, then execute the measured
segment sampler on exactly its cached fresh inner packet. -/
namespace Blotto.PlayerSpecificNestedSpecDrawExecution
open PlayerSpecificDensePolynomial PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicNestedInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def run (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ)
    (bits : Fin ((17*H+K)+K) → Bool) : FixedArrayTable 3 Data×ℕ :=
  let packet:=PlayerSpecificNestedPacketExecution.run model 18 H K bits
  let profile:=PlayerSpecificNestedSpecProfileExecution.run model root a K packet.1.2
  let sampled:=PlayerSpecificSegmentDrawExecution.run model root profile.1 17 H K packet.1.1
  (sampled.1,packet.2+profile.2+sampled.2+price model [.control 1])

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ) (bits : Fin ((17*H+K)+K) → Bool) :
    (run model root a H K bits).1=PlayerSpecificAlgebraicNestedSpecDraw.draw model root a H K bits := by
  simp only [run,PlayerSpecificNestedPacketExecution.value,PlayerSpecificNestedSpecProfileExecution.value,
    PlayerSpecificSegmentDrawExecution.value,PlayerSpecificAlgebraicNestedSpecDraw.draw]
theorem packing (model : RationalCostModel) : price model [.control 1]=2 := rfl

theorem price_equation (model : RationalCostModel) (root : Candidate) (a : Input) (H K : ℕ) (bits : Fin ((17*H+K)+K) → Bool) :
    (run model root a H K bits).2=(PlayerSpecificNestedPacketExecution.run model 18 H K bits).2+
      (PlayerSpecificNestedSpecProfileExecution.run model root a K (secondBitBlock (17*H+K) K bits)).2+
      (PlayerSpecificSegmentDrawExecution.run model root
        (PlayerSpecificAlgebraicNestedSpecProfile.prepare model root a K (secondBitBlock (17*H+K) K bits)) 17 H K
        (firstBitBlock (17*H+K) K bits)).2+2 := by
  simp only [run,PlayerSpecificNestedPacketExecution.value,PlayerSpecificNestedSpecProfileExecution.value,packing]

end Blotto.PlayerSpecificNestedSpecDrawExecution
