import Blotto.PlayerSpecificRationalFiniteMeasuredExecution

/-! Every code reached by the floor search has O(P)-bit dyadic
threshold operands, including its one-past-top boundary code. -/
namespace Blotto.PlayerSpecificOutputFloorSourceSizes
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem code_width (P code : ℕ) (hc : code≤2^P) :
    binaryWordWidth code≤P+2 ∧ binaryWordWidth (code+1)≤P+2 := by
  have hp : 1≤2^P := Nat.one_le_two_pow
  have hcap : code+1≤2^(P+1) := by
    rw [pow_succ]
    omega
  have hw := binaryWordWidth_mono hcap
  rw [PlayerSpecificIsolationDepthHeight.two_power_width] at hw
  exact ⟨(binaryWordWidth_mono (by omega : code≤code+1)).trans (by omega),by omega⟩

theorem threshold_height (P code : ℕ) (hc : code≤2^P) :
    RationalHeight (PlayerSpecificAlgebraicOutputFloor.threshold P code) (P+2) := by
  have hp : 0<2^P := Nat.two_pow_pos P
  have hn : code+1<2^(P+2) := by
    rw [pow_add]
    norm_num only [Nat.reducePow]
    omega
  have hd : 2^P<2^(P+2) := by
    rw [pow_add]
    norm_num only [Nat.reducePow]
    omega
  have h := RationalHeight.fraction ((code+1:ℕ):ℤ) (2^P) (P+2) hp
    (by simpa only [Int.natAbs_natCast] using hn) hd
  simpa only [PlayerSpecificAlgebraicOutputFloor.threshold,Int.cast_natCast,
    Nat.cast_pow,Nat.cast_ofNat] using h

theorem operands_height (P code : ℕ) (hc : code≤2^P) :
    RationalHeight ((code+1:ℕ):ℚ) (P+2) ∧
    RationalHeight ((2^P:ℕ):ℚ) (P+2) := by
  have hp : 0<2^P := Nat.two_pow_pos P
  have hn : code+1<2^(P+2) := by
    rw [pow_add]
    norm_num only [Nat.reducePow]
    omega
  have hd : 2^P<2^(P+2) := by
    rw [pow_add]
    norm_num only [Nat.reducePow]
    omega
  have hone : 1<2^(P+2) := by omega
  constructor
  · have h:=RationalHeight.fraction ((code+1:ℕ):ℤ) 1 (P+2) (by decide)
      (by simpa only [Int.natAbs_natCast] using hn) hone
    simpa only [Int.cast_natCast,Nat.cast_one,div_one] using h
  · have h:=RationalHeight.fraction ((2^P:ℕ):ℤ) 1 (P+2) (by decide)
      (by simpa only [Int.natAbs_natCast] using hd) hone
    simpa only [Int.cast_natCast,Nat.cast_one,div_one] using h

end Blotto.PlayerSpecificOutputFloorSourceSizes
