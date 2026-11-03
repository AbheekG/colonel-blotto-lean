import Blotto.BinaryNestedSpecFactoryWork
import Blotto.BinaryFourSpecSampler

/-! Native four-input sorting retains the three actual comparison results and
one forward/inverse coordinate permutation. Its regime guard retains complement
and threshold arithmetic. Primitive prices follow original stored field
heights; permutation/copy/index representation costs remain separate. -/

namespace Blotto.BinaryFourNativeOrderWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode BinaryFactoryHeight

def compareWithWork (length : Fin 3 → SignedWord) (i j : Fin 3) : Equiv.Perm (Fin 3) × ℕ :=
  (BinaryFourSpecSampler.comparePermutation length i j,BinaryRationalArithmetic.lessEqualWork (length i) (length j))

def sortWithWork (length : Fin 3 → SignedWord) : Equiv.Perm (Fin 3) × ℕ :=
  let first := compareWithWork length 0 1
  let middle := fun j => length (first.1 j)
  let second := compareWithWork middle 1 2
  let last := fun j => middle (second.1 j)
  let third := compareWithWork last 0 1
  ((third.1.trans second.1).trans first.1,first.2 + second.2 + third.2)

theorem sortWithWork_state (length : Fin 3 → SignedWord) :
    (sortWithWork length).1 = BinaryFourSpecSampler.sortPermutation length := rfl

theorem sortWithWork_bound (length : Fin 3 → SignedWord) (hC : ∀ j, CanonicalWord (length j))
    (s : ℕ) (hH : ∀ j, RationalHeight (value (length j)) s) : (sortWithWork length).2 ≤ 3 * compareBound s := by
  have h1 := comparator_bound (length 0) (length 1) (hC 0) (hC 1) s (hH 0) (hH 1)
  have h2 := comparator_bound (length (BinaryFourSpecSampler.comparePermutation length 0 1 1))
    (length (BinaryFourSpecSampler.comparePermutation length 0 1 2)) (hC _) (hC _) s (hH _) (hH _)
  have h3 := comparator_bound
    (length (BinaryFourSpecSampler.comparePermutation length 0 1 (BinaryFourSpecSampler.comparePermutation
      (fun j => length (BinaryFourSpecSampler.comparePermutation length 0 1 j)) 1 2 0)))
    (length (BinaryFourSpecSampler.comparePermutation length 0 1 (BinaryFourSpecSampler.comparePermutation
      (fun j => length (BinaryFourSpecSampler.comparePermutation length 0 1 j)) 1 2 1))) (hC _) (hC _) s (hH _) (hH _)
  unfold sortWithWork compareWithWork
  dsimp only
  omega

def orderedWithWork (input : BinaryFourSpecSampler.Input) :
    (BinaryFourParameters.Input × Equiv.Perm (Fin 4)) × ℕ :=
  let sorted := sortWithWork input.length.read
  ((⟨input.B,input.length.read (sorted.1 0),input.length.read (sorted.1 1),input.length.read (sorted.1 2),input.ell,input.p⟩,
    (rationalPermutationWithLast sorted.1).symm),sorted.2)

theorem orderedWithWork_state (input : BinaryFourSpecSampler.Input) :
    (orderedWithWork input).1 = (BinaryFourSpecSampler.orderedInput input,BinaryFourSpecSampler.permutation input) := rfl

theorem orderedWithWork_bound (input : BinaryFourSpecSampler.Input) (hC : input.Canonical) (s : ℕ)
    (hH : ∀ j, RationalHeight (value (input.length.read j)) s) : (orderedWithWork input).2 ≤ 3 * compareBound s :=
  sortWithWork_bound input.length.read hC.2.1 s hH

def InputHeight (input : BinaryFourParameters.Input) (s : ℕ) : Prop := RationalHeight (value input.B) s ∧
  RationalHeight (value input.u) s ∧ RationalHeight (value input.v) s ∧ RationalHeight (value input.w) s ∧
  RationalHeight (value input.ell) s ∧ RationalHeight (value input.p) s

theorem input_height_of_refines (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hR : input.Refines source) (s : ℕ) (h : source.FieldsHeight s) : InputHeight input s := by
  unfold InputHeight
  rw [hR.1,hR.2.1,hR.2.2.1,hR.2.2.2.1,hR.2.2.2.2.1,hR.2.2.2.2.2]
  exact h

def guardWithWork (input : BinaryFourParameters.Input) : Bool × ℕ :=
  let complement := applyWithWork .sub BinaryExpressionCompiler.Constant.one.word input.p
  let threshold := applyWithWork .mul complement.1 input.ell
  (BinaryRationalArithmetic.lessEqual threshold.1 input.w,
    complement.2 + threshold.2 + BinaryRationalArithmetic.lessEqualWork threshold.1 input.w)

theorem guardWithWork_state (input : BinaryFourParameters.Input) : (guardWithWork input).1 = BinaryFourParentCompiler.gluingCase input := by
  unfold guardWithWork BinaryFourParentCompiler.gluingCase
  simp only [applyWithWork_state]

def guardBound (s : ℕ) : ℕ := 2 * opcodeBound (expressionHeightBudget s 1) + compareBound (expressionHeightBudget s 2)

theorem guardWithWork_bound (input : BinaryFourParameters.Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : InputHeight input s) : (guardWithWork input).2 ≤ guardBound s := by
  have hOneC := BinaryExpressionCompiler.Constant.word_canonical .one
  have hOne := one_height s hs
  have hCompC := BinaryReflectedFourSetup.opcode_canonical .sub _ _ hOneC hC.2.2.2.2.2
  have hm1 := expressionHeightBudget_ge_input s 1
  have hm2 := expressionHeightBudget_ge_input s 2
  have hComp : RationalHeight (value (apply .sub BinaryExpressionCompiler.Constant.one.word input.p)) (expressionHeightBudget s 1) := by
    rw [apply_value .sub _ _ hOneC.1 hC.2.2.2.2.2.1]
    have h1 : RationalHeight (value BinaryExpressionCompiler.Constant.one.word) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hOne
    have h2 : RationalHeight (value input.p) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hH.2.2.2.2.2
    exact h1.sub_level h2
  have hThresholdC := BinaryReflectedFourSetup.opcode_canonical .mul _ _ hCompC hC.2.2.2.2.1
  have hThreshold : RationalHeight (value (apply .mul (apply .sub BinaryExpressionCompiler.Constant.one.word input.p) input.ell))
      (expressionHeightBudget s 2) := by
    rw [apply_value .mul _ _ hCompC.1 hC.2.2.2.2.1.1]
    exact hComp.mul_level (hH.2.2.2.2.1.mono hm1)
  have hSub := opcode_bound .sub _ _ hOneC hC.2.2.2.2.2 _ (hOne.mono hm1) (hH.2.2.2.2.2.mono hm1)
  have hMul := opcode_bound .mul _ _ hCompC hC.2.2.2.2.1 _ hComp (hH.2.2.2.2.1.mono hm1)
  have hGuard := comparator_bound _ input.w hThresholdC hC.2.2.2.1 _ hThreshold (hH.2.2.2.1.mono hm2)
  unfold guardWithWork guardBound
  simp only [applyWithWork_state]
  omega

end Blotto.BinaryFourNativeOrderWork
