import Blotto.PlayerSpecificSegmentSelectionEntryExecution

/-! All segment-entry analysis widths are polynomial in the actual
original weight height, finite slot count and coin precision. -/
namespace Blotto.PlayerSpecificSegmentSelectionEntrySizes
open PlayerSpecificSegmentSelectionSizes
set_option autoImplicit false
set_option maxHeartbeats 2500000

def massSize (slots T : ℕ) : ℕ := PlayerSpecificAlgebraicHeightEnvelope.step T+(slots+1)*(T+1)+slots+10
def coefficient : ℕ := (PlayerSpecificAlgebraicHeightEnvelope.coefficient+12)*(PlayerSpecificAlgebraicHeightEnvelope.coefficient+15)

theorem lower (slots T : ℕ) : T≤massSize slots T ∧ 1≤massSize slots T ∧
    PlayerSpecificAlgebraicHeightEnvelope.step T+(slots+1)*(T+1)≤massSize slots T := by
  have h:=PlayerSpecificAlgebraicHeightEnvelope.large T
  dsimp [massSize]
  omega

theorem mass_linear (slots T : ℕ) : massSize slots T+1≤
    (PlayerSpecificAlgebraicHeightEnvelope.coefficient+13)*(slots+1)*(T+1) := by
  dsimp [massSize,PlayerSpecificAlgebraicHeightEnvelope.step]
  nlinarith only [Nat.zero_le (PlayerSpecificAlgebraicHeightEnvelope.coefficient*slots*(T+1)),
    Nat.zero_le (slots*T),Nat.zero_le slots,Nat.zero_le T]

theorem additive (C slots T H S : ℕ) (h : S+1≤C*(slots+1)*(T+1)) :
    S+H+slots+1≤(C+2)*(slots+1)*(T+H+1) := by
  nlinarith only [h,Nat.zero_le (C*slots*H),Nat.zero_le (C*H),Nat.zero_le (slots*T),
    Nat.zero_le (slots*H),Nat.zero_le slots,Nat.zero_le T,Nat.zero_le H]

theorem size_bound (slots T H : ℕ) : size (massSize slots T) H slots+1≤coefficient*(slots+1)*(T+H+1) := by
  have ha:=additive _ slots T H _ (mass_linear slots T)
  have hs:=size_linear (massSize slots T) H slots
  exact hs.trans (by simpa only [coefficient,Nat.add_assoc,Nat.mul_assoc] using
    Nat.mul_le_mul_left (PlayerSpecificAlgebraicHeightEnvelope.coefficient+12) ha)

theorem transfer (C B slots A U K : ℕ) (hK : K≤2) (hU : U+1≤B*(slots+1)*A) :
    (slots+1)^K*C*(U+1)^3≤(C*B^3)*(slots+1)^5*A^3 := by
  have hk : (slots+1)^K≤(slots+1)^2 := Nat.pow_le_pow_right (by omega) hK
  have hp:=Nat.mul_le_mul (Nat.mul_le_mul_right C hk) (Nat.pow_le_pow_left hU 3)
  exact hp.trans_eq (by ring)

theorem loop_transfer (C B slots A U : ℕ) (hU : U+1≤B*(slots+1)*A) :
    (slots+1)*(C*(slots+1)*(U+1)^3)≤(C*B^3)*(slots+1)^5*A^3 := by
  have hp:=transfer C B slots A U 2 (by omega) hU
  convert hp using 1
  ring

theorem constant_transfer (C R B slots A U : ℕ) (hU : U+1≤B*(slots+1)*A) :
    (C*R)*(U+1)^3≤((C*R)*B^3)*(slots+1)^5*A^3 := by
  simpa only [pow_zero,Nat.one_mul] using transfer (C*R) B slots A U 0 (by omega) hU

theorem frame_transfer (C R B slots A U : ℕ) (hU : U+1≤B*(slots+1)*A) :
    ((C*(slots+1))*R)*(U+1)^3≤((C*R)*B^3)*(slots+1)^5*A^3 := by
  have hp:=transfer (C*R) B slots A U 1 (by omega) hU
  simpa only [pow_one,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hp

end Blotto.PlayerSpecificSegmentSelectionEntrySizes
