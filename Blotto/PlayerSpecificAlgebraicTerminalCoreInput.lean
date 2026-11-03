import Blotto.PlayerSpecificAlgebraicTerminalEmbedding

/-! Actual group-core inputs retain three cached totals and compute the
optional fractional quotient once. Validity is a proof-only interface to
be derived from the reached terminal resource state. -/
namespace Blotto.PlayerSpecificAlgebraicTerminalCoreInput
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicCandidates (Candidate)
open scoped BigOperators
set_option autoImplicit false

structure Input where
  budget : Data
  lengths : FixedArrayTable 3 Data
  count : ℕ
  fractional : Option (Data × Data)

def prepare {N : ℕ} (p : PlayerSpecificAlgebraicInitialVector.Result N) (s : State N) (B : ℚ)
    (g : PlayerSpecificAlgebraicTerminalPreparation.Prepared N) : Input :=
  let lengths : FixedArrayTable 3 Data := FixedArrayTable.ofFn (fun j =>
    ((g.groups[j.val]?).map (fun h => h.total)).getD [])
  let fractional := g.fractional.map (fun j => ((p.rows.read j).length,
    PlayerSpecificAlgebraicField.divide p.parameters.root.polynomial (s.data.read j) (p.rows.read j).length))
  ⟨PlayerSpecificAlgebraicField.constant p.parameters.root.polynomial B,lengths,g.groups.length,fractional⟩

def uniformThree (root : Candidate) (a : Input) : PlayerSpecificAlgebraicThreeInput.Input :=
  ⟨a.budget,a.lengths.read 0,a.lengths.read 1,a.lengths.read 2,PlayerSpecificAlgebraicField.constant root.polynomial 1⟩

def mixedThree (a : Input) (ell probability : Data) : PlayerSpecificAlgebraicThreeInput.Input :=
  ⟨a.budget,a.lengths.read 0,a.lengths.read 1,ell,probability⟩

def mixedFour (a : Input) (ell probability : Data) : PlayerSpecificAlgebraicFourSpecInput.Input :=
  ⟨a.budget,a.lengths,ell,probability⟩

noncomputable def groupSum (a : Input) (x : ℝ) : ℝ :=
  ∑ j : Fin 3,if j.val < a.count then realEvaluate (a.lengths.read j) x else 0

structure Valid (a : Input) (x : ℝ) : Prop where
  count : a.count=2 ∨ a.count=3
  budget : 0 < realEvaluate a.budget x
  lengths : ∀ j : Fin 3,j.val < a.count → 0 < realEvaluate (a.lengths.read j) x ∧ realEvaluate (a.lengths.read j) x ≤ realEvaluate a.budget x
  uniform : a.fractional=none → groupSum a x=2*realEvaluate a.budget x
  mixed : ∀ ell probability,a.fractional=some (ell,probability) →
    0 < realEvaluate ell x ∧ realEvaluate ell x ≤ realEvaluate a.budget x ∧
      0 < realEvaluate probability x ∧ realEvaluate probability x < 1 ∧
      groupSum a x+realEvaluate probability x*realEvaluate ell x=2*realEvaluate a.budget x

theorem sum_two (a : Input) (x : ℝ) (h : a.count=2) :
    groupSum a x=realEvaluate (a.lengths.read 0) x+realEvaluate (a.lengths.read 1) x := by
  simp [groupSum,h,Fin.sum_univ_succ]

theorem sum_three (a : Input) (x : ℝ) (h : a.count=3) :
    groupSum a x=realEvaluate (a.lengths.read 0) x+realEvaluate (a.lengths.read 1) x+realEvaluate (a.lengths.read 2) x := by
  simp [groupSum,h,Fin.sum_univ_succ,add_assoc]

noncomputable def uniformSpec (a : Input) (x : ℝ) (h : Valid a x) (hc : a.count=3) (hn : a.fractional=none) : UniformGroupSpec 3 where
  B := realEvaluate a.budget x
  length := values a.lengths x
  B_pos := h.budget
  length_pos := fun j => (h.lengths j (by rw [hc]; exact j.isLt)).1
  length_le := fun j => (h.lengths j (by rw [hc]; exact j.isLt)).2
  balance := by
    have hm := h.uniform hn
    rw [sum_three a x hc] at hm
    simpa [values,Fin.sum_univ_succ,add_assoc] using hm

noncomputable def mixedSpecTwo (a : Input) (x : ℝ) (h : Valid a x) (hc : a.count=2)
    (ell probability : Data) (hf : a.fractional=some (ell,probability)) : MixedGroupSpec 2 where
  B := realEvaluate a.budget x
  length := fun j => realEvaluate (a.lengths.read j.castSucc) x
  ell := realEvaluate ell x
  p := realEvaluate probability x
  B_pos := h.budget
  length_pos := fun j => (h.lengths j.castSucc (by rw [hc]; exact j.isLt)).1
  length_le := fun j => (h.lengths j.castSucc (by rw [hc]; exact j.isLt)).2
  ell_pos := (h.mixed ell probability hf).1
  ell_le := (h.mixed ell probability hf).2.1
  p_pos := (h.mixed ell probability hf).2.2.1
  p_lt := (h.mixed ell probability hf).2.2.2.1
  balance := by
    have hm := (h.mixed ell probability hf).2.2.2.2
    rw [sum_two a x hc] at hm
    simpa [Fin.sum_univ_succ] using hm

noncomputable def mixedSpecThree (a : Input) (x : ℝ) (h : Valid a x) (hc : a.count=3)
    (ell probability : Data) (hf : a.fractional=some (ell,probability)) : MixedGroupSpec 3 where
  B := realEvaluate a.budget x
  length := values a.lengths x
  ell := realEvaluate ell x
  p := realEvaluate probability x
  B_pos := h.budget
  length_pos := fun j => (h.lengths j (by rw [hc]; exact j.isLt)).1
  length_le := fun j => (h.lengths j (by rw [hc]; exact j.isLt)).2
  ell_pos := (h.mixed ell probability hf).1
  ell_le := (h.mixed ell probability hf).2.1
  p_pos := (h.mixed ell probability hf).2.2.1
  p_lt := (h.mixed ell probability hf).2.2.2.1
  balance := by
    have hm := (h.mixed ell probability hf).2.2.2.2
    rw [sum_three a x hc] at hm
    simpa [values,Fin.sum_univ_succ,add_assoc] using hm

theorem uniform_values (root : Candidate) (a : Input) (x : ℝ) (hx : realEvaluate root.polynomial x=0)
    (h : Valid a x) (hc : a.count=3) (hn : a.fractional=none) :
    PlayerSpecificAlgebraicUnorderedThree.Values (uniformThree root a) (uniformSpec a x h hc hn).threeInput x := by
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  simp only [uniformThree,PlayerSpecificAlgebraicField.constant_value _ _ x hx,Rat.cast_one,UniformGroupSpec.threeInput]

theorem mixed_two_values (a : Input) (x : ℝ) (h : Valid a x) (hc : a.count=2)
    (ell probability : Data) (hf : a.fractional=some (ell,probability)) :
    PlayerSpecificAlgebraicUnorderedThree.Values (mixedThree a ell probability) (mixedSpecTwo a x h hc ell probability hf).threeInput x :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem mixed_three_values (a : Input) (x : ℝ) (h : Valid a x) (hc : a.count=3)
    (ell probability : Data) (hf : a.fractional=some (ell,probability)) :
    PlayerSpecificAlgebraicFourSpecInput.Values (mixedFour a ell probability) (mixedSpecThree a x h hc ell probability hf).fourInput x :=
  ⟨rfl,fun _ => rfl,rfl,rfl⟩

end Blotto.PlayerSpecificAlgebraicTerminalCoreInput
