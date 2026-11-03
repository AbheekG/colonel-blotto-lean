import Blotto.PlayerSpecificAlgebraicOutputFloorBounds

/-! The actual output is precisely 2^-P floor(2^P x), and its reduced
rational height is linear in P. No real floor is executed at runtime. -/
namespace Blotto.PlayerSpecificAlgebraicOutputFloorSpecification
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicOutputFloor PlayerSpecificAlgebraicOutputFloorBounds
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem index_eq_floor (root : Candidate) (a : Data) (P : ℕ)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : 0 ≤ realEvaluate a x ∧ realEvaluate a x ≤ 1) :
    (search root a P).1=⌊(2:ℝ)^P*realEvaluate a x⌋₊ := by
  have h := index_bounds root a P hm hirr hv x hx ha
  dsimp only at h
  have hp : (0:ℝ) < (2:ℝ)^P := pow_pos (by norm_num) _
  apply Eq.symm
  apply (Nat.floor_eq_iff (mul_nonneg hp.le ha.1)).mpr
  have hl := (div_le_iff₀ hp).mp h.2.1
  have hu := (lt_div_iff₀ hp).mp h.2.2
  simp only [Nat.cast_add,Nat.cast_one] at hu
  exact ⟨by simpa only [mul_comm] using hl,by simpa only [mul_comm] using hu⟩

theorem height (root : Candidate) (a : Data) (P : ℕ)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : 0 ≤ realEvaluate a x ∧ realEvaluate a x ≤ 1) :
    RationalHeight (PlayerSpecificAlgebraicOutputFloor.round root a P) (P+2) := by
  have h := (index_bounds root a P hm hirr hv x hx ha).1
  have hp : 2^P < 2^(P+2) := by
    rw [pow_add]
    norm_num only [Nat.reducePow]
    have hpos := Nat.two_pow_pos P
    omega
  have hn : ((search root a P).1:ℤ).natAbs < 2^(P+2) := by
    simpa only [Int.natAbs_natCast] using h.trans_lt hp
  have hf := RationalHeight.fraction ((search root a P).1:ℤ) (2^P) (P+2) (Nat.two_pow_pos P) hn hp
  simpa only [PlayerSpecificAlgebraicOutputFloor.round,Int.cast_natCast,Nat.cast_pow,Nat.cast_ofNat] using hf

end Blotto.PlayerSpecificAlgebraicOutputFloorSpecification
