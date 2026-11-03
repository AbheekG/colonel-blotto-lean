import Blotto.BinaryPRGPhysicalRawRequestLifetime
import Blotto.BinaryPRGCheckedGameLifetime

/-! Original-frame polynomial for the retained source trace of the physical
raw parser. Native allocator and bit-machine costs are separate. -/
namespace Blotto.BinaryTerminalPhysicalRawPolynomial
set_option maxHeartbeats 2000000

theorem preparation_bound (n : ℕ) :
    PRGPhysicalArrayInterface.preparationBound n ≤
      100000000*(n+4)^5 := by
  have h : PRGPhysicalArrayInterface.preparationBound n+
      (102399998848+127999994588*n+63999298592*n^2+
        15971794336*n^3+1978140800*n^4+95723200*n^5) =
        100000000*(n+4)^5 := by
    unfold PRGPhysicalArrayInterface.preparationBound
      PRGPhysicalArrayInterface.heapCap
    ring
  omega

theorem checked_game_envelope_bound (n : ℕ) :
    BinaryPRGPhysicalCheckedGameLifetime.envelope n ≤
      BinaryPRGCheckedGameLifetime.envelope n+
        2*PRGPhysicalArrayInterface.preparationBound n+4*n+144 := by
  unfold BinaryPRGPhysicalCheckedGameLifetime.envelope
    BinaryPRGCheckedGameLifetime.envelope
    BinaryPRGCheckedPreparationLifetime.envelope
  omega

theorem raw_envelope_bound (n : ℕ) :
    BinaryPRGPhysicalRawRequestLifetime.envelope n ≤
      500000000000000*(n+4)^8 := by
  let T := n+4
  have hOld := BinaryPRGCheckedGameLifetime.envelope_polynomial n
  have hCompare := checked_game_envelope_bound n
  have hPrep := preparation_bound n
  have hT : 0 < T := by dsimp only [T]; omega
  have hPow : T^5 ≤ T^8 := Nat.pow_le_pow_right hT (by decide)
  have hPrepTop : PRGPhysicalArrayInterface.preparationBound n ≤
      100000000*T^8 :=
    hPrep.trans (Nat.mul_le_mul_left 100000000 hPow)
  have hLinear : n ≤ T^8 := by
    have hn : n ≤ T := by dsimp only [T]; omega
    exact hn.trans (by simpa only [pow_one] using
      Nat.pow_le_pow_right hT (by decide : 1 ≤ 8))
  have hOne : 1 ≤ T^8 := Nat.one_le_pow 8 T (by omega)
  unfold BinaryPRGPhysicalRawRequestLifetime.envelope
    BinaryAccuracyLifetime.envelope
  change BinaryPRGPhysicalCheckedGameLifetime.envelope n+
      2048*(n+8)+100000*(n+1001)+256 ≤
      500000000000000*T^8
  change BinaryPRGCheckedGameLifetime.envelope n ≤
    400000000000000*T^8 at hOld
  omega

theorem uniform_envelope : ∃ C d : ℕ, ∀ n,
    BinaryPRGPhysicalRawRequestLifetime.envelope n ≤ C*(n+1)^d := by
  refine ⟨500000000000000*4^8,8,?_⟩
  intro n
  have h := raw_envelope_bound n
  have hp := Nat.mul_le_mul_left 500000000000000
    (Nat.pow_le_pow_left (show n+4 ≤ 4*(n+1) by omega) 8)
  rw [Nat.mul_pow] at hp
  exact h.trans (hp.trans_eq (by ring))

end Blotto.BinaryTerminalPhysicalRawPolynomial
