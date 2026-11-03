import Blotto.NestedEndpoints

/-! Exact parameter checks for manuscript Lemma 2.4. These construct its
auxiliary three-variable inputs; four-variable composition remains separate. -/

namespace Blotto
open MeasureTheory Set

structure FourInput where
  B : ℝ
  u : ℝ
  v : ℝ
  w : ℝ
  ell : ℝ
  p : ℝ
  u_pos : 0 < u
  uv : u ≤ v
  vw : v ≤ w
  ell_pos : 0 < ell
  p_pos : 0 < p
  p_lt : p < 1
  w_le : w ≤ B
  ell_le : ell ≤ B
  balance : u + v + w + p * ell = 2 * B

namespace FourInput

noncomputable def S (i : FourInput) : ℝ := i.u + i.v + i.w
noncomputable def auxLength (i : FourInput) : ℝ :=
  max (max (max (i.v - i.u) (i.w - i.p * i.ell)) ((2 - i.p) * i.ell - i.w)) 0
noncomputable def firstBudget (i : FourInput) : ℝ := (i.u + i.v + i.auxLength) / 2
noncomputable def secondBudget (i : FourInput) : ℝ := (i.auxLength + i.w + i.p * i.ell) / 2

theorem lengths_positive (i : FourInput) : 0 < i.v ∧ 0 < i.w ∧ 0 < i.B ∧ 0 < i.S := by
  have hv := lt_of_lt_of_le i.u_pos i.uv
  have hw := lt_of_lt_of_le hv i.vw
  exact ⟨hv, hw, lt_of_lt_of_le hw i.w_le, by dsimp [S]; linarith [i.u_pos]⟩

theorem auxLength_lower (i : FourInput) :
    0 ≤ i.auxLength ∧ i.v - i.u ≤ i.auxLength ∧
      i.w - i.p * i.ell ≤ i.auxLength ∧ (2 - i.p) * i.ell - i.w ≤ i.auxLength := by
  unfold auxLength
  exact ⟨le_max_right _ _,
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _),
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _),
    le_trans (le_max_right _ _) (le_max_left _ _)⟩

theorem auxLength_pos (i : FourInput) : 0 < i.auxLength := by
  have hl := i.auxLength_lower
  have ht := mul_pos (sub_pos.mpr i.p_lt) i.ell_pos
  by_contra h
  have hn := le_of_not_gt h
  nlinarith

theorem auxLength_upper (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    i.auxLength ≤ i.u + i.v ∧ i.auxLength ≤ i.w + i.p * i.ell := by
  have hu := i.u_pos
  have hv := i.lengths_positive.1
  have hw := i.lengths_positive.2.1
  have hp := mul_pos i.p_pos i.ell_pos
  constructor
  · simp only [auxLength, max_le_iff]
    repeat' constructor
    all_goals nlinarith [i.balance, i.w_le, i.ell_le]
  · simp only [auxLength, max_le_iff]
    repeat' constructor
    all_goals nlinarith [i.vw]

theorem auxiliary_budget_bounds (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    0 < i.firstBudget ∧ i.u ≤ i.firstBudget ∧ i.v ≤ i.firstBudget ∧
      i.auxLength ≤ i.firstBudget ∧ 0 < i.secondBudget ∧
      i.auxLength ≤ i.secondBudget ∧ i.w ≤ i.secondBudget ∧ i.ell ≤ i.secondBudget := by
  have hl := i.auxLength_lower
  have hu := i.auxLength_upper hcase
  have hd := i.auxLength_pos
  have hw := i.lengths_positive.2.1
  have hp := mul_pos i.p_pos i.ell_pos
  dsimp [firstBudget, secondBudget]
  repeat' constructor
  all_goals linarith [i.u_pos, i.uv]

theorem auxiliary_budget_sum (i : FourInput) : i.firstBudget + i.secondBudget - i.auxLength = i.B := by
  dsimp [firstBudget, secondBudget]
  linarith [i.balance]

/-- Both actual three-variable coupling laws needed by the gluing case exist.
The conditional gluing and finite segment refinement are still required. -/
theorem auxiliary_couplings (i : FourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) :
    ∃ μ ν : Mixed 3,
      (∀ᵐ x ∂(μ : Measure (Allocation 3)), FullBudget i.firstBudget x) ∧
      (∀ᵐ x ∂(ν : Measure (Allocation 3)), FullBudget i.secondBudget x) ∧
      (marginal μ 0 : Measure ℝ) = uniformLaw i.u ∧
      (marginal μ 1 : Measure ℝ) = uniformLaw i.v ∧
      (marginal μ 2 : Measure ℝ) = uniformLaw i.auxLength ∧
      (marginal ν 0 : Measure ℝ) = uniformLaw i.auxLength ∧
      (marginal ν 1 : Measure ℝ) = uniformLaw i.w ∧
      (marginal ν 2 : Measure ℝ) = zeroUniformLaw i.ell i.p := by
  have hb := i.auxiliary_budget_bounds hcase
  rcases exists_three_coupling i.firstBudget i.u i.v i.auxLength 1 hb.1 i.u_pos
    i.lengths_positive.1 i.auxLength_pos (by norm_num)
    hb.2.1 hb.2.2.1 hb.2.2.2.1 le_rfl (by dsimp [firstBudget]; ring)
    with ⟨μ, hμ, h0, h1, h2⟩
  rcases exists_three_coupling i.secondBudget i.auxLength i.w i.ell i.p
    hb.2.2.2.2.1 i.auxLength_pos i.lengths_positive.2.1 i.ell_pos i.p_pos
    hb.2.2.2.2.2.1 hb.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2
    (le_of_lt i.p_lt) (by dsimp [secondBudget]; ring)
    with ⟨ν, hν, h3, h4, h5⟩
  refine ⟨μ, ν, hμ, hν, h0, h1, ?_, h3, h4, h5⟩
  simpa [zeroUniformLaw] using h2

theorem small_case_bounds (i : FourInput) (hcase : i.w < (1 - i.p) * i.ell) :
    (2 - i.p) * i.ell ≤ i.S ∧ i.S < 3 * ((1 - i.p) * i.ell) ∧
      i.p < 1 / 2 ∧ i.p * i.ell < i.u ∧ i.p * i.ell < i.S - 2 * i.w := by
  have hS : (2 - i.p) * i.ell ≤ i.S := by dsimp [S]; nlinarith [i.balance, i.ell_le]
  have hSup : i.S < 3 * ((1 - i.p) * i.ell) := by dsimp [S]; nlinarith [i.uv, i.vw]
  have h2p : 2 * i.p < 1 := by
    by_contra h
    have hn := le_of_not_gt h
    have hm := mul_le_mul_of_nonneg_right hn (le_of_lt i.ell_pos)
    nlinarith
  refine ⟨hS, hSup, by linarith, ?_, ?_⟩
  · dsimp [S] at hS
    nlinarith [i.vw]
  · dsimp [S] at hS ⊢
    nlinarith

end FourInput
end Blotto
