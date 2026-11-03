import Blotto.BinaryFactoryHeight

/-! Actual segment padding/translation/mixture assembly retains original bytes.
Primitive translation and mixture prices are derived from field heights. The
mixture caches its common complement once. Copies/access/ownership are separate. -/

namespace Blotto.BinaryAssemblyArithmeticWork
open BinaryRationalNormalization BinaryRationalEncoding BinaryRationalOpcode BinaryStoredOverlapEnvironment
open BinaryFactoryHeight
open scoped BigOperators

theorem pad_height {n k : ℕ} (table : Segment n k) (m : ℕ) (fallback : Fin k) (s : ℕ) (hs : 3 ≤ s)
    (h : SegmentHeight table s) : SegmentHeight (BinarySegmentAssembly.padRight table m fallback) s := by
  refine ⟨?_,?_⟩
  · intro slot
    simp only [BinarySegmentAssembly.padRight,FixedArrayTable.read_ofFn]
    refine Fin.addCases ?_ ?_ slot
    · intro j; simpa using h.1 j
    · intro j; simpa using zero_height s hs
  · intro slot j
    simp only [BinarySegmentAssembly.padRight,FixedArrayTable.read_ofFn]
    refine Fin.addCases ?_ ?_ slot
    · intro i; simpa using h.2 i j
    · intro i; simpa using h.2 fallback j

def shiftWork {k : ℕ} (table : Segment 3 k) (x : SignedWord) : ℕ :=
  (∑ slot, (applyWithWork .add ((table.P.read slot).read 2) x).2) +
    (∑ slot, (applyWithWork .add ((table.Q.read slot).read 2) x).2)

theorem shiftWork_bound {k : ℕ} (table : Segment 3 k) (x : SignedWord) (hC : table.Canonical)
    (hX : CanonicalWord x) (s : ℕ) (h : SegmentHeight table s) (hx : RationalHeight (value x) s) :
    shiftWork table x ≤ 2 * k * opcodeBound s := by
  have hp := fun slot => opcode_bound .add _ _ (hC.2.1 slot 2) hX s (h.2 slot 2).1 hx
  have hq := fun slot => opcode_bound .add _ _ (hC.2.2 slot 2) hX s (h.2 slot 2).2 hx
  have hP := (Finset.sum_le_sum (fun slot _ => hp slot)).trans_eq (show (∑ _slot : Fin k, opcodeBound s) = k * opcodeBound s by simp)
  have hQ := (Finset.sum_le_sum (fun slot _ => hq slot)).trans_eq (show (∑ _slot : Fin k, opcodeBound s) = k * opcodeBound s by simp)
  unfold shiftWork
  nlinarith

theorem shift_height {k : ℕ} (table : Segment 3 k) (x : SignedWord) (hC : table.Canonical)
    (hX : CanonicalWord x) (s : ℕ) (h : SegmentHeight table s) (hx : RationalHeight (value x) s) :
    SegmentHeight (BinarySegmentAssembly.shiftThird table x) (expressionHeightBudget s 1) := by
  have hm := expressionHeightBudget_ge_input s 1
  refine ⟨fun slot => (h.1 slot).mono hm,?_⟩
  intro slot j
  simp only [BinarySegmentAssembly.shiftThird,FixedArrayTable.read_ofFn]
  fin_cases j
  · exact ⟨(h.2 slot 0).1.mono hm,(h.2 slot 0).2.mono hm⟩
  · exact ⟨(h.2 slot 1).1.mono hm,(h.2 slot 1).2.mono hm⟩
  · constructor
    · change RationalHeight (value (apply .add ((table.P.read slot).read 2) x)) _
      rw [apply_value .add _ _ (hC.2.1 slot 2).1 hX.1]
      have hp : RationalHeight (value ((table.P.read slot).read 2)) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using (h.2 slot 2).1
      have ht : RationalHeight (value x) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hx
      exact hp.add_level ht
    · change RationalHeight (value (apply .add ((table.Q.read slot).read 2) x)) _
      rw [apply_value .add _ _ (hC.2.2 slot 2).1 hX.1]
      have hp : RationalHeight (value ((table.Q.read slot).read 2)) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using (h.2 slot 2).2
      have ht : RationalHeight (value x) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hx
      exact hp.add_level ht

def binaryWithWork {n k m : ℕ} (p : SignedWord) (first : Segment n k) (second : Segment n m) : Segment n (k + m) × ℕ :=
  let complement := applyWithWork .sub BinaryExpressionCompiler.Constant.one.word p
  let left := FixedArrayTable.ofFn (fun j => applyWithWork .mul p (first.weight.read j))
  let right := FixedArrayTable.ofFn (fun j => applyWithWork .mul complement.1 (second.weight.read j))
  (⟨FixedArrayTable.ofFn (Fin.addCases (fun j => (left.read j).1) (fun j => (right.read j).1)),
    FixedArrayTable.ofFn (Fin.addCases first.P.read second.P.read),
    FixedArrayTable.ofFn (Fin.addCases first.Q.read second.Q.read)⟩,
    complement.2 + (∑ j, (left.read j).2) + (∑ j, (right.read j).2))

theorem binaryWithWork_state {n k m : ℕ} (p : SignedWord) (first : Segment n k) (second : Segment n m) :
    (binaryWithWork p first second).1 = BinarySegmentAssembly.binary p first second := by
  unfold binaryWithWork BinarySegmentAssembly.binary
  simp only [FixedArrayTable.read_ofFn,applyWithWork_state]

theorem binaryWithWork_bound {n k m : ℕ} (p : SignedWord) (first : Segment n k) (second : Segment n m)
    (hP : CanonicalWord p) (hC : first.Canonical) (hD : second.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hp : RationalHeight (value p) s) (hf : SegmentHeight first s) (hg : SegmentHeight second s) :
    (binaryWithWork p first second).2 ≤ (k + m + 1) * opcodeBound (expressionHeightBudget s 1) := by
  let H := expressionHeightBudget s 1
  have hm := expressionHeightBudget_ge_input s 1
  have hOne := one_height s hs
  have hOneC := BinaryExpressionCompiler.Constant.word_canonical .one
  have hComplementC := BinaryReflectedFourSetup.opcode_canonical .sub _ _ hOneC hP
  have hComplement : RationalHeight (value (applyWithWork .sub BinaryExpressionCompiler.Constant.one.word p).1) H := by
    rw [applyWithWork_state,apply_value .sub _ _ hOneC.1 hP.1]
    have h1 : RationalHeight (value BinaryExpressionCompiler.Constant.one.word) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hOne
    have h2 : RationalHeight (value p) (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using hp
    exact h1.sub_level h2
  have hc := opcode_bound .sub _ _ hOneC hP H (hOne.mono hm) (hp.mono hm)
  have hl := fun j => opcode_bound .mul p (first.weight.read j) hP (hC.1 j) H (hp.mono hm) ((hf.1 j).mono hm)
  have hr := fun j => opcode_bound .mul (applyWithWork .sub BinaryExpressionCompiler.Constant.one.word p).1 (second.weight.read j)
    (by rw [applyWithWork_state]; exact hComplementC) (hD.1 j) H hComplement ((hg.1 j).mono hm)
  have hL := (Finset.sum_le_sum (fun j _ => hl j)).trans_eq (show (∑ _j : Fin k, opcodeBound H) = k * opcodeBound H by simp)
  have hR := (Finset.sum_le_sum (fun j _ => hr j)).trans_eq (show (∑ _j : Fin m, opcodeBound H) = m * opcodeBound H by simp)
  unfold binaryWithWork
  simp only [FixedArrayTable.read_ofFn]
  dsimp only [H] at hc hL hR
  nlinarith

end Blotto.BinaryAssemblyArithmeticWork
