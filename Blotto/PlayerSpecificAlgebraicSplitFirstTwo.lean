import Blotto.PlayerSpecificAlgebraicFourGluingDraw

/-! Actual proportional splitting of a merged coordinate caches its
denominator and both fractions once. The remaining two rows are reused. -/
namespace Blotto.PlayerSpecificAlgebraicSplitFirstTwo
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def split (root : Candidate) (a d : Data) (y : FixedArrayTable 3 Data) : FixedArrayTable 4 Data :=
  let denominator := PlayerSpecificAlgebraicField.plus root.polynomial a d
  let first := PlayerSpecificAlgebraicField.divide root.polynomial a denominator
  let second := PlayerSpecificAlgebraicField.divide root.polynomial d denominator
  FixedArrayTable.ofFn ![PlayerSpecificAlgebraicField.times root.polynomial first (y.read 0),
    PlayerSpecificAlgebraicField.times root.polynomial second (y.read 0),y.read 1,y.read 2]

theorem value (root : Candidate) (a d : Data) (y : FixedArrayTable 3 Data)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial)) (x : ℝ)
    (hx : realEvaluate root.polynomial x=0) :
    values (split root a d y) x=splitFirstTwo (realEvaluate a x) (realEvaluate d x) (values y x) := by
  have hm0 : root.polynomial ≠ [] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  have hd := PlayerSpecificAlgebraicField.plus_reduced root.polynomial a d hm hm0
  funext j
  fin_cases j <;> simp [split,values,FixedArrayTable.read_ofFn,splitFirstTwo,
    PlayerSpecificAlgebraicField.times_value _ _ _ x hx,
    PlayerSpecificAlgebraicField.divide_value _ _ _ hm hirr hd x hx,
    PlayerSpecificAlgebraicField.plus_value _ _ _ x hx]

theorem budget (root : Candidate) (a d : Data) (y : FixedArrayTable 3 Data)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial)) (x B : ℝ)
    (hx : realEvaluate root.polynomial x=0) (ha : 0 < realEvaluate a x) (hd : 0 < realEvaluate d x)
    (hy : FullBudget B (values y x)) : FullBudget B (values (split root a d y) x) := by
  rw [value root a d y hm hirr x hx]
  exact splitFirstTwo_fullBudget ha hd hy

theorem bounds (root : Candidate) (a d : Data) (y : FixedArrayTable 3 Data) (T : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 1 ≤ T)
    (ha : Reduced root.polynomial a ∧ HasHeight a T) (hd : Reduced root.polynomial d ∧ HasHeight d T)
    (hy : ∀ j,Reduced root.polynomial (y.read j) ∧ HasHeight (y.read j) T) :
    ∀ j,Reduced root.polynomial ((split root a d y).read j) ∧ HasHeight ((split root a d y).read j) (iterate 3 T) := by
  have hstep : T ≤ step T := (Nat.le_succ _).trans (large T)
  have htwo : T ≤ iterate 2 T := PlayerSpecificAlgebraicExpressionBudget.initial_le 2 T
  have hthree : T ≤ iterate 3 T := PlayerSpecificAlgebraicExpressionBudget.initial_le 3 T
  let denom := PlayerSpecificAlgebraicField.plus root.polynomial a d
  have hdenom := PlayerSpecificAlgebraicField.plus_reduced root.polynomial a d hm hm0
  have hdenomh := (PlayerSpecificAlgebraicExpressionBudget.binary_heights RationalCostModel.schoolbook root a d T
    hm hm0 hml ha.1 hd.1 hmT ha.2 hd.2 hT).1
  have hf : ∀ z,Reduced root.polynomial z → HasHeight z T →
      Reduced root.polynomial (PlayerSpecificAlgebraicField.divide root.polynomial z denom) ∧
      HasHeight (PlayerSpecificAlgebraicField.divide root.polynomial z denom) (iterate 2 T) := by
    intro z hz hzh
    exact ⟨PlayerSpecificAlgebraicField.divide_reduced _ _ _ hm hm0,
      divide_height root.polynomial z denom (step T) hm hm0 hml hz hdenom
        (mono hmT hstep) (mono hzh hstep) hdenomh (hT.trans hstep)⟩
  have hmultiply : ∀ z,Reduced root.polynomial z → HasHeight z T →
      Reduced root.polynomial (PlayerSpecificAlgebraicField.times root.polynomial
        (PlayerSpecificAlgebraicField.divide root.polynomial z denom) (y.read 0)) ∧
      HasHeight (PlayerSpecificAlgebraicField.times root.polynomial
        (PlayerSpecificAlgebraicField.divide root.polynomial z denom) (y.read 0)) (iterate 3 T) := by
    intro z hz hzh
    have hfrac := hf z hz hzh
    exact ⟨PlayerSpecificAlgebraicField.times_reduced _ _ _ hm hm0,
      times_height root.polynomial _ _ (iterate 2 T) hm hm0 hml hfrac.1 (hy 0).1
        (mono hmT htwo) hfrac.2 (mono (hy 0).2 htwo)⟩
  intro j
  fin_cases j <;> simp only [split,FixedArrayTable.read_ofFn]
  · exact hmultiply a ha.1 ha.2
  · exact hmultiply d hd.1 hd.2
  · exact ⟨(hy 1).1,mono (hy 1).2 hthree⟩
  · exact ⟨(hy 2).1,mono (hy 2).2 hthree⟩

end Blotto.PlayerSpecificAlgebraicSplitFirstTwo
