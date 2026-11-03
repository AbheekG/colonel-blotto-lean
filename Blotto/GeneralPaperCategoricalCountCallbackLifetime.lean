import Blotto.GeneralPaperCategoricalProductLifetime

/-! Actual categorical count callback activation: the loaded rational word,
retained denominator, quotient/product words, local primitive scratch and all
numeric/control fields. No magnitude bound is substituted for a word bound. -/
namespace Blotto.GeneralPaperCategoricalCountCallbackLifetime
open GeneralPaperEncodedScalarStorage (natBits fields)
set_option autoImplicit false
set_option maxHeartbeats 1800000

def footprint {r : ℕ} (weights : FixedArrayTable r ℚ) (model : RationalCostModel) (A D : ℕ) (i : Fin r) : ℕ :=
  let q := weights.read i
  let quotient := GeneralPaperNaturalScalarStep.run model A .div D q.den
  let product := GeneralPaperNaturalScalarStep.run model A .mul q.num.toNat quotient.1
  let actual := GeneralPaperStoredCategoricalCounts.coordinate weights model A D i
  rationalWordWidth q + GeneralPaperNaturalScalarLifetime.footprint model A .div D q.den +
    GeneralPaperNaturalScalarLifetime.footprint model A .mul q.num.toNat quotient.1 +
    fields A [D, q.den, q.num.toNat, quotient.1, product.1, quotient.2, product.2, actual.2, i.val] + 128 * A

theorem bounded {r : ℕ} (weights : FixedArrayTable r ℚ) (model : RationalCostModel) (A D : ℕ) (i : Fin r) :
    footprint weights model A D i ≤ 256 * (GeneralPaperStoredCategoricalCounts.coordinate weights model A D i).2 := by
  let q := weights.read i
  let quotient := GeneralPaperNaturalScalarStep.run model A .div D q.den
  let product := GeneralPaperNaturalScalarStep.run model A .mul q.num.toNat quotient.1
  let F := (GeneralPaperStoredCategoricalCounts.coordinate weights model A D i).2
  have hF : F = rationalWordWidth q + quotient.2 + product.2 + 64 * (A + binaryWordWidth (i.val + 1) + 1) := rfl
  have hDiv := GeneralPaperNaturalScalarLifetime.words model A .div D q.den
  change natBits D + natBits q.den + natBits quotient.1 + 16 * A + 16 ≤ quotient.2 at hDiv
  have hMul := GeneralPaperNaturalScalarLifetime.words model A .mul q.num.toNat quotient.1
  change natBits q.num.toNat + natBits quotient.1 + natBits product.1 + 16 * A + 16 ≤ product.2 at hMul
  have hDivSpace := GeneralPaperNaturalScalarLifetime.bounded model A .div D q.den
  change GeneralPaperNaturalScalarLifetime.footprint model A .div D q.den ≤ 32 * quotient.2 at hDivSpace
  have hMulSpace := GeneralPaperNaturalScalarLifetime.bounded model A .mul q.num.toNat quotient.1
  change GeneralPaperNaturalScalarLifetime.footprint model A .mul q.num.toNat quotient.1 ≤ 32 * product.2 at hMulSpace
  have hIndex : natBits i.val ≤ 1 + binaryWordWidth (i.val + 1) :=
    Nat.add_le_add_left (binaryWordWidth_mono (Nat.le_succ i.val)) 1
  have hWord (x : ℕ) (hx : x ≤ F) : natBits x ≤ F + 2 :=
    (GeneralPaperNaturalScalarLifetime.counter_word x).trans (by omega)
  have hFields := GeneralPaperEncodedScalarStorage.fields_bound A (F + 2)
    [D, q.den, q.num.toNat, quotient.1, product.1, quotient.2, product.2, F, i.val] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · omega
      · omega
      · omega
      · omega
      · omega
      · exact hWord _ (by omega)
      · exact hWord _ (by omega)
      · exact hWord _ le_rfl
      · omega)
  change fields A _ ≤ 9 * (F + 2 + A) + 32 * A at hFields
  change rationalWordWidth q + GeneralPaperNaturalScalarLifetime.footprint model A .div D q.den +
    GeneralPaperNaturalScalarLifetime.footprint model A .mul q.num.toNat quotient.1 +
    fields A [D, q.den, q.num.toNat, quotient.1, product.1, quotient.2, product.2, F, i.val] + 128 * A ≤ 256 * F
  omega

theorem written {r : ℕ} (weights : FixedArrayTable r ℚ) (model : RationalCostModel) (A D : ℕ) (i : Fin r) :
    natBits (GeneralPaperStoredCategoricalCounts.coordinate weights model A D i).1 ≤
      (GeneralPaperStoredCategoricalCounts.coordinate weights model A D i).2 := by
  have h := GeneralPaperNaturalScalarLifetime.written model A .mul (weights.read i).num.toNat
    (GeneralPaperNaturalScalarStep.run model A .div D (weights.read i).den).1
  unfold GeneralPaperStoredCategoricalCounts.coordinate
  dsimp only
  omega

theorem native_height_bound {n r s : ℕ} {l : RationalSegmentLottery n r} (p : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A D : ℕ)
    (hD : D = GeneralPaperEqualCategoricalIntegerData.denominator p.lottery.weight)
    (h : ∀ i, RationalHeight (p.weights.read i) s) (i : Fin r) :
    footprint p.weights model A D i ≤ 256 * GeneralPaperStoredCategoricalCounts.stepBound model A r s :=
  (bounded p.weights model A D i).trans (Nat.mul_le_mul_left 256
    (GeneralPaperStoredCategoricalCounts.coordinate_work p model A D hD h i))

end Blotto.GeneralPaperCategoricalCountCallbackLifetime
