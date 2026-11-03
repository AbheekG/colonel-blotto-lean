import Blotto.PlayerSpecificAlgebraicCoinExpectation

/-! The actual flat resource/segment packet decomposes into its first
H bits and the remaining flat packet. This matches the executing list
of blocks, with an exact independent iterated expectation. -/
namespace Blotto.PlayerSpecificFlatCoinBlocks
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem packet_equality (C H : ℕ) : (C+1)*H=H+C*H := by ring

def headBits (C H : ℕ) (bits : Fin ((C+1)*H) → Bool) : Fin H → Bool :=
  fun j => bits ⟨j.val,by rw [packet_equality]; have hj := j.isLt; omega⟩

def restBits (C H : ℕ) (bits : Fin ((C+1)*H) → Bool) : Fin (C*H) → Bool :=
  fun j => bits ⟨H+j.val,by rw [packet_equality]; have hj := j.isLt; omega⟩

def castPacket (C H : ℕ) (bits : Fin ((C+1)*H) → Bool) : Fin (H+C*H) → Bool :=
  fun j => bits (Fin.cast (packet_equality C H).symm j)

theorem headBits_eq (C H : ℕ) (bits : Fin ((C+1)*H) → Bool) :
    headBits C H bits=firstBitBlock H (C*H) (castPacket C H bits) := by
  funext j
  apply congrArg bits
  exact Fin.ext rfl

theorem restBits_eq (C H : ℕ) (bits : Fin ((C+1)*H) → Bool) :
    restBits C H bits=secondBitBlock H (C*H) (castPacket C H bits) := by
  funext j
  apply congrArg bits
  exact Fin.ext rfl

theorem blocks_cons (C H : ℕ) (bits : Fin ((C+1)*H) → Bool) :
    PlayerSpecificFiniteResourceLoop.blocks (C+1) H bits=
      headBits C H bits::PlayerSpecificFiniteResourceLoop.blocks C H (restBits C H bits) := by
  unfold PlayerSpecificFiniteResourceLoop.blocks
  rw [List.ofFn_succ]
  congr 1
  · funext j
    apply congrArg bits
    exact Fin.ext (by simp)
  · apply congrArg List.ofFn
    funext i
    funext j
    change bits ⟨(i.val+1)*H+j.val,_⟩=bits ⟨H+(i.val*H+j.val),_⟩
    apply congrArg bits
    apply Fin.ext
    dsimp only
    ring

theorem integral_cast (R S : ℕ) (e : R=S) (f : (Fin S → Bool) → ℝ) :
    (∫ bits,f (fun j => bits (Fin.cast e.symm j)) ∂(fairBitLaw R : Measure (Fin R → Bool)))=
      ∫ bits,f bits ∂(fairBitLaw S : Measure (Fin S → Bool)) := by
  subst S
  rfl

theorem integral_blocks (C H : ℕ) (f : (Fin H → Bool) → (Fin (C*H) → Bool) → ℝ) :
    (∫ bits,f (headBits C H bits) (restBits C H bits) ∂(fairBitLaw ((C+1)*H) : Measure (Fin ((C+1)*H) → Bool)))=
      ∫ first,(∫ rest,f first rest ∂(fairBitLaw (C*H) : Measure (Fin (C*H) → Bool)))
        ∂(fairBitLaw H : Measure (Fin H → Bool)) := by
  simp_rw [headBits_eq,restBits_eq]
  exact (integral_cast ((C+1)*H) (H+C*H) (packet_equality C H)
    (fun bits => f (firstBitBlock H (C*H) bits) (secondBitBlock H (C*H) bits))).trans
      (PlayerSpecificFairBitBlocks.integral_blocks H (C*H) f)

theorem binary_continuation (C H : ℕ) (coin : (Fin H → Bool) → Bool)
    (upper lower : (Fin (C*H) → Bool) → ℝ) :
    (∫ bits,(if coin (headBits C H bits) then upper (restBits C H bits) else lower (restBits C H bits))
      ∂(fairBitLaw ((C+1)*H) : Measure (Fin ((C+1)*H) → Bool)))=
      PlayerSpecificFairBitBlocks.success H coin*(∫ bits,upper bits ∂(fairBitLaw (C*H) : Measure (Fin (C*H) → Bool)))+
        (1-PlayerSpecificFairBitBlocks.success H coin)*(∫ bits,lower bits ∂(fairBitLaw (C*H) : Measure (Fin (C*H) → Bool))) := by
  simp_rw [headBits_eq,restBits_eq]
  exact (integral_cast ((C+1)*H) (H+C*H) (packet_equality C H)
    (fun bits => if coin (firstBitBlock H (C*H) bits) then upper (secondBitBlock H (C*H) bits) else lower (secondBitBlock H (C*H) bits))).trans
      (PlayerSpecificFairBitBlocks.binary_continuation H (C*H) coin upper lower)

end Blotto.PlayerSpecificFlatCoinBlocks
