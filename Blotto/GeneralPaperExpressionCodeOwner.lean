import Blotto.GeneralPaperEqualRouteOwner

/-! Encoded ownership of fixed expression syntax, including both branches.
Unlike execution counts, nodes includes both conditional continuations. It
depends only on static code; runtime numerical inputs are not duplicated. -/
namespace Blotto.GeneralPaperExpressionCodeOwner
open GeneralPaperEncodedScalarStorage (natBits)
set_option autoImplicit false
set_option maxHeartbeats 1600000

def nodes {k : ℕ} : RationalExpression k → ℕ
  | .input _ | .literal _ => 1
  | .add a b | .sub a b | .mul a b | .div a b | .minimum a b | .maximum a b => nodes a + nodes b + 1
  | .ifLe a b yes no => nodes a + nodes b + nodes yes + nodes no + 1

theorem depth_bound {k : ℕ} (e : RationalExpression k) : nodes e + 1 ≤ 2 * 4 ^ e.depth := by
  induction e with
  | input j => exact le_rfl
  | literal q => exact le_rfl
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
    have hA := ha.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide : 0 < (4 : ℕ)) (le_max_left a.depth b.depth)))
    have hB := hb.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide : 0 < (4 : ℕ)) (le_max_right a.depth b.depth)))
    simp only [nodes, RationalExpression.depth, pow_succ]
    nlinarith only [hA, hB]
  | ifLe a b yes no ha hb hy hn =>
    let d := max (max a.depth b.depth) (max yes.depth no.depth)
    have hA := ha.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide : 0 < (4 : ℕ))
      (show a.depth ≤ d by dsimp [d]; omega)))
    have hB := hb.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide : 0 < (4 : ℕ))
      (show b.depth ≤ d by dsimp [d]; omega)))
    have hY := hy.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide : 0 < (4 : ℕ))
      (show yes.depth ≤ d by dsimp [d]; omega)))
    have hN := hn.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide : 0 < (4 : ℕ))
      (show no.depth ≤ d by dsimp [d]; omega)))
    change nodes a + nodes b + nodes yes + nodes no + 1 + 1 ≤ 2 * 4 ^ (d + 1)
    rw [pow_succ]
    omega

def footprint {k : ℕ} (A : ℕ) : RationalExpression k → ℕ
  | .input j => 64 * A + natBits j.val
  | .literal q => 64 * A + rationalWordWidth q
  | .add a b | .sub a b | .mul a b | .div a b | .minimum a b | .maximum a b =>
      64 * A + footprint A a + footprint A b
  | .ifLe a b yes no => 64 * A + footprint A a + footprint A b + footprint A yes + footprint A no

def unit (A k s : ℕ) : ℕ := 64 * A + natBits k + 1 + 2 * s

theorem bounded {k : ℕ} (A s : ℕ) (e : RationalExpression k) (h : e.LiteralHeights s) :
    footprint A e ≤ nodes e * unit A k s := by
  induction e with
  | input j =>
    have hJ := Nat.add_le_add_left (binaryWordWidth_mono j.isLt.le) 1
    change natBits j.val ≤ natBits k at hJ
    simp only [footprint, nodes, one_mul]
    unfold unit
    omega
  | literal q =>
    have hQ := rationalWordWidth_of_height h
    simp only [footprint, nodes, one_mul]
    unfold unit
    omega
  | add a b ha hb | sub a b ha hb | mul a b ha hb | div a b ha hb | minimum a b ha hb | maximum a b ha hb =>
    have hA := ha h.1
    have hB := hb h.2
    simp only [footprint, nodes]
    have hUnit : 64 * A ≤ unit A k s := by unfold unit; omega
    nlinarith only [hA, hB, hUnit]
  | ifLe a b yes no ha hb hy hn =>
    have hA := ha h.1
    have hB := hb h.2.1
    have hY := hy h.2.2.1
    have hN := hn h.2.2.2
    simp only [footprint, nodes]
    have hUnit : 64 * A ≤ unit A k s := by unfold unit; omega
    nlinarith only [hA, hB, hY, hN, hUnit]

theorem fixed_depth {k : ℕ} (A s d : ℕ) (e : RationalExpression k) (h : e.LiteralHeights s) (hd : e.depth ≤ d) :
    footprint A e ≤ 2 * 4 ^ d * unit A k s := by
  have hNodes := depth_bound e
  have hDepth := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide : 0 < (4 : ℕ)) hd)
  exact (bounded A s e h).trans (Nat.mul_le_mul_right _ (by omega))

end Blotto.GeneralPaperExpressionCodeOwner
