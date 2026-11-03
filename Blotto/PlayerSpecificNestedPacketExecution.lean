import Blotto.PlayerSpecificNestedInteriorProfileSourceCost

/-! Nested packet counts execute once before inner/outer slices are
materialized. Every bit address, cached view and count return is priced. -/
namespace Blotto.PlayerSpecificNestedPacketExecution
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def frame (slots H K headBits innerBits totalBits : ℕ) : Trace :=
  PlayerSpecificAlgebraicCallerFrame.run [] [slots,H,K,headBits,innerBits,totalBits]

def run (model : RationalCostModel) (slots H K : ℕ) (bits : Fin (((slots-1)*H+K)+K) → Bool) :
    ((Fin ((slots-1)*H+K) → Bool)×(Fin K → Bool))×ℕ :=
  let headBits:=PlayerSpecificNaturalExecution.binary model (fun a b => a*b) (slots-1) H
  let innerBits:=PlayerSpecificNaturalExecution.binary model (fun a b => a+b) headBits.1 K
  let totalBits:=PlayerSpecificNaturalExecution.binary model (fun a b => a+b) innerBits.1 K
  let inner:=PlayerSpecificBitSliceExecution.run model totalBits.1 0 innerBits.1 (by change 0+((slots-1)*H+K)≤((slots-1)*H+K)+K; omega) bits
  let outer:=PlayerSpecificBitSliceExecution.run model totalBits.1 innerBits.1 K (Nat.le_refl _) bits
  ((inner.1,outer.1),headBits.2+innerBits.2+totalBits.2+inner.2+outer.2+
    price model (frame slots H K headBits.1 innerBits.1 totalBits.1))

theorem value (model : RationalCostModel) (slots H K : ℕ) (bits : Fin (((slots-1)*H+K)+K) → Bool) :
    (run model slots H K bits).1=(firstBitBlock ((slots-1)*H+K) K bits,secondBitBlock ((slots-1)*H+K) K bits) := by
  dsimp only [run,PlayerSpecificNaturalExecution.binary]
  simp only [PlayerSpecificBitSliceExecution.first_value,PlayerSpecificBitSliceExecution.second_value]

end Blotto.PlayerSpecificNestedPacketExecution
