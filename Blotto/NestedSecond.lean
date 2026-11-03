import Blotto.NestedSecondIdentity
import Blotto.ThreePoint

/-! The second nested case: a binary mixture of F_T's proved first-case
coupling and a translated three-uniform coupling. The zero-weight uniform
component is omitted when T=t. -/

namespace Blotto.NestedInput
open MeasureTheory Set

noncomputable def secondUniformInput (i : NestedInput) (htu : i.u ≤ i.t)
    (hTt : i.mirrorLength < i.t) : ThreeInput where
  B := i.M - i.mirrorLength
  a := i.a
  d := i.d
  c := i.t - i.mirrorLength
  p := 1
  B_pos := by
    have hT := i.mirrorLength_bounds htu
    have hv := hT.2.1
    dsimp [v] at hv
    linarith [i.d_pos]
  a_pos := i.a_pos
  d_pos := i.d_pos
  c_pos := sub_pos.mpr hTt
  p_pos := by norm_num
  a_le := by
    have hT := i.mirrorLength_bounds htu
    have hU : i.mirrorLength ≤ i.u := le_trans hT.2.1 i.lengths.2.1
    dsimp [u] at hU
    linarith
  d_le := by
    have hV := (i.mirrorLength_bounds htu).2.1
    dsimp [v] at hV
    linarith
  c_le := by linarith [i.t_lt, i.c_le]
  p_le := le_rfl
  ordered := i.ordered
  balance := by dsimp [mirrorLength, u, v]; ring

noncomputable def secondUniformLaw (i : NestedInput) (htu : i.u ≤ i.t)
    (hTt : i.mirrorLength < i.t) : Mixed 3 :=
  shiftedLaw i.mirrorLength (i.secondUniformInput htu hTt).couplingLaw

theorem secondUniformLaw_contract (i : NestedInput) (htu : i.u ≤ i.t)
    (hTt : i.mirrorLength < i.t) :
    (∀ᵐ x ∂(i.secondUniformLaw htu hTt : Measure (Allocation 3)), FullBudget i.M x) ∧
    (marginal (i.secondUniformLaw htu hTt) 0 : Measure ℝ) = uniformLaw i.a ∧
    (marginal (i.secondUniformLaw htu hTt) 1 : Measure ℝ) = uniformLaw i.d ∧
    (marginal (i.secondUniformLaw htu hTt) 2 : Measure ℝ) =
      (affineUniform i.mirrorLength i.t : Measure ℝ) := by
  let hi := i.secondUniformInput htu hTt
  have hB : hi.B + i.mirrorLength = i.M := by dsimp [hi, secondUniformInput]; ring
  have hm := hi.couplingLaw_marginals
  constructor
  · simpa only [secondUniformLaw, hB] using shiftedLaw_fullBudget
      (le_of_lt (i.mirrorLength_bounds htu).1) hi.couplingLaw_fullBudget
  constructor
  · rw [secondUniformLaw, shiftedLaw_marginal_zero, hm.1]
    rfl
  constructor
  · rw [secondUniformLaw, shiftedLaw_marginal_one, hm.2.1]
    rfl
  · rw [secondUniformLaw, shiftedLaw_marginal_two, hm.2.2]
    change Measure.map (fun x => x + i.mirrorLength) (zeroUniformLaw (i.t - i.mirrorLength) 1) = _
    rw [shift_zeroUniformLaw i.mirrorLength i.t 1 hTt]
    simp

noncomputable def secondLaw (i : NestedInput) (htu : i.u ≤ i.t) : Mixed 3 :=
  if hTt : i.mirrorLength < i.t then
    binaryLaw i.secondAlpha ⟨le_of_lt (i.secondAlpha_bounds htu).1, (i.secondAlpha_bounds htu).2⟩
      (i.familyFirstLaw i.mirrorLength (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1)
      (i.secondUniformLaw htu hTt)
  else i.familyFirstLaw i.mirrorLength (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1

theorem second_coupling_contract (i : NestedInput) (htu : i.u ≤ i.t) :
    (∀ᵐ x ∂(i.secondLaw htu : Measure (Allocation 3)), FullBudget i.M x) ∧
      (marginal (i.secondLaw htu) 0 : Measure ℝ) = uniformLaw i.a ∧
      (marginal (i.secondLaw htu) 1 : Measure ℝ) = uniformLaw i.d ∧
      (marginal (i.secondLaw htu) 2 : Measure ℝ) = i.nestedTargetLaw := by
  have hT := i.mirrorLength_bounds htu
  have hf := i.familyFirstLaw_contract i.mirrorLength hT.1 hT.2.1
  unfold secondLaw
  split_ifs with hTt
  · have hu := i.secondUniformLaw_contract htu hTt
    refine ⟨binaryLaw_fullBudget _ _ _ _ hf.1 hu.1, ?_, ?_, ?_⟩
    · exact binaryLaw_marginal_common _ _ _ _ 0 _ hf.2.1 hu.2.1
    · exact binaryLaw_marginal_common _ _ _ _ 1 _ hf.2.2.1 hu.2.2.1
    · rw [binaryLaw_marginal, hf.2.2.2, hu.2.2.2]
      exact (i.second_decomposition htu).symm
  · have heq : i.mirrorLength = i.t := le_antisymm hT.2.2.1 (le_of_not_gt hTt)
    refine ⟨hf.1, hf.2.1, hf.2.2.1, ?_⟩
    rw [hf.2.2.2, heq, i.familyLaw_original]

noncomputable def secondPoint (i : NestedInput) (htu : i.u ≤ i.t) (useFamily : Bool)
    (r t : ℝ) (edge : Fin 9) : Allocation 3 :=
  if hTt : i.mirrorLength < i.t then
    if useFamily then
      i.familyFirstPoint i.mirrorLength (i.mirrorLength_bounds htu).1
        (i.mirrorLength_bounds htu).2.1 r edge t
    else shiftThird i.mirrorLength ((i.secondUniformInput htu hTt).couplingPoint edge t)
  else i.familyFirstPoint i.mirrorLength (i.mirrorLength_bounds htu).1
    (i.mirrorLength_bounds htu).2.1 r edge t

theorem secondPoint_fullBudget (i : NestedInput) (htu : i.u ≤ i.t) (useFamily : Bool)
    {r t : ℝ} (hr : 0 ≤ r ∧ r ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1) (edge : Fin 9) :
    FullBudget i.M (i.secondPoint htu useFamily r t edge) := by
  unfold secondPoint
  split_ifs with hTt hFamily
  · exact i.familyFirstPoint_fullBudget _ _ _ hr ht edge
  · have he : (i.secondUniformInput htu hTt).B + i.mirrorLength = i.M := by
      dsimp [secondUniformInput]; ring
    simpa only [he] using shiftThird_fullBudget (le_of_lt (i.mirrorLength_bounds htu).1)
      ((i.secondUniformInput htu hTt).couplingPoint_fullBudget edge ht)
  · exact i.familyFirstPoint_fullBudget _ _ _ hr ht edge

end Blotto.NestedInput
