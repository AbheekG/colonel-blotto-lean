import Blotto.PureBoundaryEquilibria

/-! Actual continuous security-loss infima over arbitrary feasible whole laws.
They are bounded, admit arbitrarily close feasible laws, and satisfy weak
constant-sum duality. The reverse inequality/minimax identity from retained
R33, including its regular-rich smoothing and compactness/separation proof,
is NOT assumed or certified here. No attainment of either infimum is built in. -/

namespace Blotto.ContinuousSecurityValues
open Set PureBoundaryEquilibria

theorem security_nonnegative {n : ℕ} (values : Values n) (budget : ℝ)
    (hBudget : 0 ≤ budget) (law : Mixed n) : 0 ≤ security values budget law :=
  (purePayoff_nonneg values (fun _ => 0) law).trans
    (purePayoff_le_security values (feasible_zero hBudget) law)

theorem security_le_one {n : ℕ} (values : Values n) (budget : ℝ)
    (hBudget : 0 ≤ budget) (law : Mixed n) : security values budget law ≤ 1 :=
  security_le values hBudget law fun row _ => purePayoff_le_one values row law

noncomputable def lossSet {n : ℕ} (values : Values n) (ownBudget opposingBudget : ℝ) : Set ℝ :=
  (fun law => security values opposingBudget law) '' {law : Mixed n | Supported ownBudget law}

noncomputable def lossInfimum {n : ℕ} (values : Values n) (ownBudget opposingBudget : ℝ) : ℝ :=
  sInf (lossSet values ownBudget opposingBudget)

theorem lossSet_nonempty {n : ℕ} (values : Values n) (ownBudget opposingBudget : ℝ)
    (hOwn : 0 ≤ ownBudget) : (lossSet values ownBudget opposingBudget).Nonempty := by
  refine ⟨security values opposingBudget (pointLaw (fun _ => 0)), ?_⟩
  exact ⟨pointLaw (fun _ => 0), pointLaw_supported _ _ (feasible_zero hOwn), rfl⟩

theorem lossSet_bddBelow {n : ℕ} (values : Values n) (ownBudget opposingBudget : ℝ)
    (hOpposing : 0 ≤ opposingBudget) : BddBelow (lossSet values ownBudget opposingBudget) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨law, _hLaw, rfl⟩
  exact security_nonnegative values opposingBudget hOpposing law

theorem lossInfimum_le_of_supported {n : ℕ} (values : Values n) (ownBudget opposingBudget : ℝ)
    (hOpposing : 0 ≤ opposingBudget) (law : Mixed n) (hLaw : Supported ownBudget law) :
    lossInfimum values ownBudget opposingBudget ≤ security values opposingBudget law :=
  csInf_le (lossSet_bddBelow values ownBudget opposingBudget hOpposing) ⟨law, hLaw, rfl⟩

theorem le_lossInfimum {n : ℕ} (values : Values n) (ownBudget opposingBudget lower : ℝ)
    (hOwn : 0 ≤ ownBudget)
    (hLower : ∀ law : Mixed n, Supported ownBudget law → lower ≤ security values opposingBudget law) :
    lower ≤ lossInfimum values ownBudget opposingBudget := by
  apply le_csInf (lossSet_nonempty values ownBudget opposingBudget hOwn)
  rintro _ ⟨law, hLaw, rfl⟩
  exact hLower law hLaw

theorem lossInfimum_nonnegative {n : ℕ} (values : Values n) (ownBudget opposingBudget : ℝ)
    (hOwn : 0 ≤ ownBudget) (hOpposing : 0 ≤ opposingBudget) :
    0 ≤ lossInfimum values ownBudget opposingBudget :=
  le_lossInfimum values ownBudget opposingBudget 0 hOwn
    fun law _ => security_nonnegative values opposingBudget hOpposing law

theorem lossInfimum_le_one {n : ℕ} (values : Values n) (ownBudget opposingBudget : ℝ)
    (hOwn : 0 ≤ ownBudget) (hOpposing : 0 ≤ opposingBudget) :
    lossInfimum values ownBudget opposingBudget ≤ 1 :=
  (lossInfimum_le_of_supported values ownBudget opposingBudget hOpposing
    (pointLaw (fun _ => 0)) (pointLaw_supported _ _ (feasible_zero hOwn))).trans
      (security_le_one values opposingBudget hOpposing _)

theorem exists_near_optimal {n : ℕ} (values : Values n) (ownBudget opposingBudget : ℝ)
    (hOwn : 0 ≤ ownBudget) (hOpposing : 0 ≤ opposingBudget) (error : ℝ) (hError : 0 < error) :
    ∃ law : Mixed n, Supported ownBudget law ∧
      security values opposingBudget law < lossInfimum values ownBudget opposingBudget + error := by
  have h : lossInfimum values ownBudget opposingBudget <
      lossInfimum values ownBudget opposingBudget + error := by linarith
  obtain ⟨score, ⟨law, hLaw, rfl⟩, hScore⟩ :=
    (csInf_lt_iff (lossSet_bddBelow values ownBudget opposingBudget hOpposing)
      (lossSet_nonempty values ownBudget opposingBudget hOwn)).1 h
  exact ⟨law, hLaw, hScore⟩

theorem supported_security_sum_ge_one {n : ℕ} (values : Values n) (budgetA budgetB : ℝ)
    (lawA lawB : Mixed n) (hA : Supported budgetA lawA) (hB : Supported budgetB lawB) :
    1 ≤ security values budgetB lawA + security values budgetA lawB := by
  have hIncA := expected_le_security values lawA lawB hA
  have hIncB := expected_le_security values lawB lawA hB
  have hSum := expected_constant_sum values lawA lawB
  linarith

/-- The weak-duality direction holds before any continuity/minimax proof.
It does not imply that either pair of finite trainers passes its sum gate. -/
theorem lossInfimum_sum_ge_one {n : ℕ} (values : Values n) (budgetA budgetB : ℝ)
    (hA : 0 ≤ budgetA) (hB : 0 ≤ budgetB) :
    1 ≤ lossInfimum values budgetA budgetB + lossInfimum values budgetB budgetA := by
  have hAgainst : ∀ lawA : Mixed n, Supported budgetA lawA →
      1 - security values budgetB lawA ≤ lossInfimum values budgetB budgetA := by
    intro lawA hLawA
    apply le_lossInfimum values budgetB budgetA _ hB
    intro lawB hLawB
    have h := supported_security_sum_ge_one values budgetA budgetB lawA lawB hLawA hLawB
    linarith
  have hOuter : 1 - lossInfimum values budgetB budgetA ≤ lossInfimum values budgetA budgetB := by
    apply le_lossInfimum values budgetA budgetB _ hA
    intro lawA hLawA
    have h := hAgainst lawA hLawA
    linarith
  linarith

end Blotto.ContinuousSecurityValues
