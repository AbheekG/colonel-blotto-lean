import Blotto.GeneralPaperExpressionCodeOwner

/-! Retain the fixed pair and three-input expression families once. Syntax
ownership includes both conditional continuations, all literal/input words,
node headers and family closures, rather than using a selected-path count. -/
namespace Blotto.GeneralPaperEqualStaticCodeOwner
open scoped BigOperators
open GeneralPaperExpressionCodeOwner (footprint unit fixed_depth)
set_option autoImplicit false
set_option maxHeartbeats 1600000

def family {n r k : ℕ} (A : ℕ) (weight : Fin r → RationalExpression k)
    (left right : Fin r → Fin n → RationalExpression k) : ℕ :=
  (∑ i, footprint A (weight i)) + (∑ i, ∑ j, footprint A (left i j)) +
    (∑ i, ∑ j, footprint A (right i j)) + 128 * A

theorem family_bound {n r k : ℕ} (A C : ℕ) (weight : Fin r → RationalExpression k)
    (left right : Fin r → Fin n → RationalExpression k)
    (hW : ∀ i, footprint A (weight i) ≤ C) (hL : ∀ i j, footprint A (left i j) ≤ C)
    (hR : ∀ i j, footprint A (right i j) ≤ C) :
    family A weight left right ≤ (r + 2 * r * n) * C + 128 * A := by
  have h1 := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hW i)
  have h2 := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hL i j))
  have h3 := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hR i j))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] at h1 h2 h3
  unfold family
  nlinarith only [h1, h2, h3]

def footprint (A : ℕ) : ℕ :=
  family A GeneralPaperPairSegmentPreparation.weight GeneralPaperPairSegmentPreparation.left GeneralPaperPairSegmentPreparation.right +
    family A GeneralPaperThreeStaticPrograms.orderedWeight GeneralPaperThreeStaticPrograms.left GeneralPaperThreeStaticPrograms.right

def profile (A : ℕ) : ℕ := 108 * (2 * 4 ^ 20 * unit A 5 2) + 256 * A

theorem bounded (A : ℕ) : footprint A ≤ profile A := by
  let C := 2 * 4 ^ 20 * unit A 5 2
  have hPair := GeneralPaperNativeSegmentCompilerLifetime.pair_bounds 0 A 2 le_rfl
    (by norm_num [RationalHeight])
  have hUnit : unit A 1 2 ≤ unit A 5 2 := by
    unfold unit GeneralPaperEncodedScalarStorage.natBits
    have h : binaryWordWidth 1 ≤ binaryWordWidth 5 := binaryWordWidth_mono (by decide)
    omega
  have hPairW (i : Fin 9) : GeneralPaperExpressionCodeOwner.footprint A (GeneralPaperPairSegmentPreparation.weight i) ≤ C := by
    exact (fixed_depth A 2 20 _ (hPair.weight_literals i) (hPair.weight_depth i |>.trans (by omega))).trans
      (Nat.mul_le_mul_left (2 * 4 ^ 20) hUnit)
  have hPairL (i : Fin 9) (j : Fin 2) : GeneralPaperExpressionCodeOwner.footprint A (GeneralPaperPairSegmentPreparation.left i j) ≤ C := by
    exact (fixed_depth A 2 20 _ (hPair.left_literals i j) (hPair.left_depth i j |>.trans (by omega))).trans
      (Nat.mul_le_mul_left (2 * 4 ^ 20) hUnit)
  have hPairR (i : Fin 9) (j : Fin 2) : GeneralPaperExpressionCodeOwner.footprint A (GeneralPaperPairSegmentPreparation.right i j) ≤ C := by
    exact (fixed_depth A 2 20 _ (hPair.right_literals i j) (hPair.right_depth i j |>.trans (by omega))).trans
      (Nat.mul_le_mul_left (2 * 4 ^ 20) hUnit)
  have hThreeW (i : Fin 9) : GeneralPaperExpressionCodeOwner.footprint A (GeneralPaperThreeStaticPrograms.orderedWeight i) ≤ C :=
    fixed_depth A 2 20 _ (GeneralPaperThreeStaticPrograms.weight_literals i) (GeneralPaperThreeStaticPrograms.weight_depth i)
  have hThreeL (i : Fin 9) (j : Fin 3) : GeneralPaperExpressionCodeOwner.footprint A (GeneralPaperThreeStaticPrograms.left i j) ≤ C :=
    fixed_depth A 2 20 _ (GeneralPaperThreeStaticPrograms.left_literals i j) (GeneralPaperThreeStaticPrograms.left_depth i j)
  have hThreeR (i : Fin 9) (j : Fin 3) : GeneralPaperExpressionCodeOwner.footprint A (GeneralPaperThreeStaticPrograms.right i j) ≤ C :=
    fixed_depth A 2 20 _ (GeneralPaperThreeStaticPrograms.right_literals i j) (GeneralPaperThreeStaticPrograms.right_depth i j)
  have h1 := family_bound A C _ _ _ hPairW hPairL hPairR
  have h2 := family_bound A C _ _ _ hThreeW hThreeL hThreeR
  change _ ≤ 108 * C + 256 * A
  unfold footprint
  omega

theorem scaling : GeneralPaperReferenceScaling.Scale profile := by unfold profile unit; fun_prop

end Blotto.GeneralPaperEqualStaticCodeOwner
