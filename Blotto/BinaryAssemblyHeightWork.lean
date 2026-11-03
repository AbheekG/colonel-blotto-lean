import Blotto.BinaryAssemblyArithmeticWork

/-! Mixture assembly propagates actual stored field heights through its cached
complement and weight products. Endpoint fields retain their original values. -/

namespace Blotto.BinaryAssemblyHeightWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode
open BinaryStoredOverlapEnvironment BinaryFactoryHeight

theorem binary_height {n k m : ℕ} (p : SignedWord) (first : Segment n k) (second : Segment n m)
    (hP : CanonicalWord p) (hC : first.Canonical) (hD : second.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hp : RationalHeight (value p) s)
    (hf : SegmentHeight first s) (hg : SegmentHeight second s) :
    SegmentHeight (BinarySegmentAssembly.binary p first second) (expressionHeightBudget s 2) := by
  have hm1 := expressionHeightBudget_ge_input s 1
  have hm2 := expressionHeightBudget_ge_input s 2
  have hOneC := BinaryExpressionCompiler.Constant.word_canonical .one
  have hComplementC := BinaryReflectedFourSetup.opcode_canonical .sub _ _ hOneC hP
  have hComplement : RationalHeight (value (apply .sub BinaryExpressionCompiler.Constant.one.word p))
      (expressionHeightBudget s 1) := by
    rw [apply_value .sub _ _ hOneC.1 hP.1]
    have h1 : RationalHeight (value BinaryExpressionCompiler.Constant.one.word) (expressionHeightBudget s 0) := by
      simpa only [expressionHeightBudget_zero] using one_height s hs
    have h2 : RationalHeight (value p) (expressionHeightBudget s 0) := by
      simpa only [expressionHeightBudget_zero] using hp
    exact h1.sub_level h2
  refine ⟨?_,?_⟩
  · intro slot
    simp only [BinarySegmentAssembly.binary,FixedArrayTable.read_ofFn]
    refine Fin.addCases ?_ ?_ slot
    · intro j
      simp only [Fin.addCases_left]
      rw [apply_value .mul _ _ hP.1 (hC.1 j).1]
      exact (hp.mono hm1).mul_level ((hf.1 j).mono hm1)
    · intro j
      simp only [Fin.addCases_right]
      rw [apply_value .mul _ _ hComplementC.1 (hD.1 j).1]
      exact hComplement.mul_level ((hg.1 j).mono hm1)
  · intro slot j
    simp only [BinarySegmentAssembly.binary,FixedArrayTable.read_ofFn]
    refine Fin.addCases ?_ ?_ slot
    · intro i; simpa using ⟨(hf.2 i j).1.mono hm2,(hf.2 i j).2.mono hm2⟩
    · intro i; simpa using ⟨(hg.2 i j).1.mono hm2,(hg.2 i j).2.mono hm2⟩

end Blotto.BinaryAssemblyHeightWork
