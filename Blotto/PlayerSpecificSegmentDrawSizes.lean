import Blotto.PlayerSpecificSegmentDrawFrameCost

/-! Complete segment-draw sizes derive from original rows, dimensions
and precisions, including the actual packet-count products. -/
namespace Blotto.PlayerSpecificSegmentDrawSizes
set_option autoImplicit false
set_option maxHeartbeats 2500000

def headCount (slots H : ℕ) : ℕ := (slots-1)*H
def packetCount (slots H K : ℕ) : ℕ := headCount slots H+K
def size (N slots T H K : ℕ) : ℕ := T+N+slots+H+K+headCount slots H+packetCount slots H K+20
def height (N slots T H K : ℕ) : ℕ := PlayerSpecificAlgebraicHeightEnvelope.iterate 3 (T+2*K+6)+
  N+slots+H+K+headCount slots H+packetCount slots H K+10
def heightCoefficient : ℕ := 7*(PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^3+1

theorem height_bound (N slots T H K : ℕ) : height N slots T H K+1≤heightCoefficient*size N slots T H K := by
  let S:=size N slots T H K
  let A:=(PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^3
  let V:=PlayerSpecificAlgebraicHeightEnvelope.iterate 3 (T+2*K+6)
  have hi : V+1≤A*(T+2*K+7) := by
    have hi0:=PlayerSpecificAlgebraicHeightEnvelope.iterate_bound 3 (T+2*K+6)
    rw [show T+2*K+6+1=T+2*K+7 by omega] at hi0
    exact hi0
  have hbase : T+2*K+7≤7*S := by dsimp [S,size]; omega
  have hrest : N+slots+H+K+headCount slots H+packetCount slots H K+10≤S := by dsimp [S,size]; omega
  have hscaled : V+1≤7*A*S := hi.trans (by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using Nat.mul_le_mul_left A hbase)
  change V+N+slots+H+K+headCount slots H+packetCount slots H K+10+1≤(7*A+1)*S
  nlinarith only [hscaled,hrest]

theorem original_size (N slots T H K : ℕ) : size N slots T H K≤24*(T+N+slots+H+K+1)^2 := by
  let A:=T+N+slots+H+K+1
  have hA : 1≤A := by dsimp [A]; omega
  have hslots : slots≤A := by dsimp [A]; omega
  have hH : H≤A := by dsimp [A]; omega
  have hK : K≤A := by dsimp [A]; omega
  have hp : headCount slots H≤A^2 :=
    (Nat.mul_le_mul_right H (Nat.sub_le slots 1)).trans (by simpa only [pow_two] using Nat.mul_le_mul hslots hH)
  have hc : packetCount slots H K≤A^2+A := by dsimp [packetCount]; omega
  have hAA : A≤A^2 := by simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left A hA
  have hOne : 1≤A^2 := Nat.succ_le_of_lt (pow_pos (by omega : 0<A) 2)
  have htotal : T+N+slots+H+K+1=A := rfl
  change T+N+slots+H+K+headCount slots H+packetCount slots H K+20≤24*A^2
  nlinarith only [hp,hc,hAA,hOne,htotal]

theorem transfer (C N slots T H K : ℕ) : C*(size N slots T H K)^8≤
    (C*24^8)*(T+N+slots+H+K+1)^16 := by
  let A:=T+N+slots+H+K+1
  have hs : size N slots T H K≤24*A^2 := original_size N slots T H K
  have hp : C*(size N slots T H K)^8≤C*(24*A^2)^8 := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hs 8)
  have heq : C*(24*A^2)^8=(C*24^8)*A^16 := by
    rw [mul_pow,←pow_mul,Nat.mul_assoc]
  exact hp.trans_eq heq

theorem power_transfer (C X S p : ℕ) (hX : X≤S) (hp : p≤8) (hS : 1≤S) : C*X^p≤C*S^8 :=
  Nat.mul_le_mul_left C ((Nat.pow_le_pow_left hX p).trans (Nat.pow_le_pow_right hS hp))

theorem selection_transfer (C x y S : ℕ) (hx : x≤S) (hy : y≤S) : C*x^5*y^3≤C*S^8 := by
  have hp:=Nat.mul_le_mul (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hx 5)) (Nat.pow_le_pow_left hy 3)
  exact hp.trans_eq (by ring)

theorem interpolation_transfer (C x y S : ℕ) (hx : x≤S) (hy : y≤7*S) : C*x*y^3≤(C*7^3)*S^4 := by
  have hp:=Nat.mul_le_mul (Nat.mul_le_mul_left C hx) (Nat.pow_le_pow_left hy 3)
  exact hp.trans_eq (by ring)

theorem frame_transfer (C R B x y z S : ℕ) (hx : x≤S) (hy : y≤S) (hz : z≤B*S) :
    ((C*x*y)*R)*z^3≤((C*R)*B^3)*S^5 := by
  have hp:=Nat.mul_le_mul (Nat.mul_le_mul_right R (Nat.mul_le_mul (Nat.mul_le_mul_left C hx) hy)) (Nat.pow_le_pow_left hz 3)
  exact hp.trans_eq (by ring)

end Blotto.PlayerSpecificSegmentDrawSizes
