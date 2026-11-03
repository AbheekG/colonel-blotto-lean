import Blotto.RationalFourSmallPreparation
import Blotto.RationalFourEntryPreparation
import Blotto.RealFourFactory

/-! Exact-real parent construction uses the same counted scalar/product
programs. Unit-price formula/access/read/write labels are explicit. Factory
repetition, indices, allocation/ownership and IEEE execution remain separate. -/

namespace Blotto.RealFourParameterTable

noncomputable def preparationWork (i : FourInput) : ℕ := 12 + RealFourParametersCode.work i + 8

theorem preparationWork_bound (i : FourInput) : preparationWork i ≤ 2068 := by
  have h := RealFourParametersCode.work_bound i
  unfold preparationWork
  omega

end Blotto.RealFourParameterTable
namespace Blotto.RealReflectedResourcePreparationCode
open scoped BigOperators

noncomputable def environment (i : FourInput) (j : Fin 3) : FixedArrayTable 4 ℝ :=
  let p := RealFourParameterTable.prepare i
  FixedArrayTable.ofFn ![p.shortFraction, p.nestedProbability, p.scaleFraction, i.originalLengths j]

theorem short_value (i : FourInput) (j : Fin 3) :
    RationalReflectedResourceCode.short.realValue (environment i j) = i.shortFraction * i.originalLengths j := by
  simp [RationalReflectedResourceCode.short, environment, FixedArrayTable.read_ofFn]

theorem initial_value (i : FourInput) (j : Fin 3) :
    RationalReflectedResourceCode.initial.realValue (environment i j) =
      i.nestedProbability * i.scaleFraction * i.originalLengths j := by
  simp [RationalReflectedResourceCode.initial, environment, FixedArrayTable.read_ofFn]

noncomputable def formulaWork (i : FourInput) : ℕ :=
  ∑ j : Fin 3, ((RationalReflectedResourceCode.short.runReal (environment i j)).2 +
    (RationalReflectedResourceCode.initial.runReal (environment i j)).2)

theorem formulaWork_bound (i : FourInput) : formulaWork i ≤ 24 := by
  have hS : RationalReflectedResourceCode.short.operationBound = 3 := by decide
  have hI : RationalReflectedResourceCode.initial.operationBound = 5 := by decide
  have h : ∀ j : Fin 3, (RationalReflectedResourceCode.short.runReal (environment i j)).2 +
      (RationalReflectedResourceCode.initial.runReal (environment i j)).2 ≤ 8 := by
    intro j
    have hs := RationalReflectedResourceCode.short.runReal_operations_le (environment i j)
    have hi := RationalReflectedResourceCode.initial.runReal_operations_le (environment i j)
    rw [hS] at hs
    rw [hI] at hi
    omega
  calc
    _ ≤ ∑ _j : Fin 3, 8 := Finset.sum_le_sum (fun j _ => h j)
    _ = _ := by simp

noncomputable def preparationWork (i : FourInput) : ℕ :=
  RealFourParameterTable.preparationWork i + formulaWork i + 20

theorem preparationWork_bound (i : FourInput) : preparationWork i ≤ 2112 := by
  have hp := RealFourParameterTable.preparationWork_bound i
  have hf := formulaWork_bound i
  unfold preparationWork
  omega

end Blotto.RealReflectedResourcePreparationCode
namespace Blotto.RealSmallUniformPreparationCode
open scoped BigOperators

noncomputable def environment (i : FourInput) (j : Fin 3) : FixedArrayTable 2 ℝ :=
  FixedArrayTable.ofFn ![(RealFourParameterTable.prepare i).scaleFraction, i.originalLengths j]

theorem value_eq (i : FourInput) (j : Fin 3) :
    RationalSmallUniformCode.product.realValue (environment i j) = i.scaleFraction * i.originalLengths j := by
  simp [RationalSmallUniformCode.product, environment, FixedArrayTable.read_ofFn]

noncomputable def formulaWork (i : FourInput) : ℕ :=
  ∑ j : Fin 3, (RationalSmallUniformCode.product.runReal (environment i j)).2

theorem formulaWork_bound (i : FourInput) : formulaWork i ≤ 9 := by
  have ho : RationalSmallUniformCode.product.operationBound = 3 := by decide
  calc
    _ ≤ ∑ _j : Fin 3, 3 := Finset.sum_le_sum (fun j _ => by
      simpa only [ho] using RationalSmallUniformCode.product.runReal_operations_le (environment i j))
    _ = _ := by simp

noncomputable def preparationWork (i : FourInput) : ℕ := RealFourParameterTable.preparationWork i + formulaWork i + 10

theorem preparationWork_bound (i : FourInput) : preparationWork i ≤ 2087 := by
  have hp := RealFourParameterTable.preparationWork_bound i
  have hf := formulaWork_bound i
  unfold preparationWork
  omega

end Blotto.RealSmallUniformPreparationCode
