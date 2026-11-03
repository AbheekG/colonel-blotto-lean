import Blotto.GeneralPaperEqualFiniteKernel
import Blotto.GeneralPaperRoundedValuePerturbation
import Blotto.GeneralPaperDyadicAccuracy

/-! A native rational heavy-field scan selects the paper's equal-budget
boundary law after positive rounding. The grouped branch is precisely the
finite midpoint segment law, with arbitrary continuous feasible deviations
and canonical half ties. This module does not assert categorical execution
or a complete preparation resource bound. -/
namespace Blotto.GeneralPaperEqualRoundedBoundary
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 700000

def scan {n : ℕ} (v : RationalFieldSelector n) : Option (Fin n) :=
  (List.finRange n).find? (fun j => decide ((1 / 2 : ℚ) ≤ v.weight j))

theorem scan_some {n : ℕ} (v : RationalFieldSelector n) (j : Fin n) (h : scan v = some j) :
    (1 / 2 : ℚ) ≤ v.weight j :=
  of_decide_eq_true (List.find?_some (p := fun a => decide ((1 / 2 : ℚ) ≤ v.weight a)) h)

theorem scan_none {n : ℕ} (v : RationalFieldSelector n) (h : scan v = none) :
    ∀ j, 2 * v.weight j ≤ 1 := by
  unfold scan at h
  simp only [List.find?_eq_none, List.mem_finRange, forall_const,
    decide_eq_true_eq, not_le] at h
  intro j
  linarith only [h j]

inductive Prepared {n : ℕ} (v : RationalFieldSelector n) where
  | dominant (chosen : Fin n) (heavy : (1 / 2 : ℚ) ≤ v.weight chosen)
  | grouped (small : ∀ j, 2 * v.weight j ≤ 1)

def prepare {n : ℕ} (v : RationalFieldSelector n) : Prepared v :=
  match h : scan v with
  | some j => .dominant j (scan_some v j h)
  | none => .grouped (scan_none v h)

noncomputable def Prepared.law {n : ℕ} {v : RationalFieldSelector n}
    (p : Prepared v) (k : ℕ) : Mixed n :=
  match p with
  | .dominant j _ => PureBoundaryEquilibria.pointLaw (PureBoundaryEquilibria.vertex 1 j)
  | .grouped small => GeneralPaperEqualFiniteKernel.law v small k

def Prepared.point {n : ℕ} {v : RationalFieldSelector n} (p : Prepared v)
    (k : ℕ) (slot : Fin 9) (fresh : Fin (k + 5) → Bool) : Fin n → ℚ :=
  match p with
  | .dominant j _ => fun a => if a = j then 1 else 0
  | .grouped small => GeneralPaperEqualFiniteKernel.point v small k slot fresh

theorem Prepared.point_fullBudget {n : ℕ} {v : RationalFieldSelector n} (p : Prepared v)
    (k : ℕ) (slot : Fin 9) (fresh : Fin (k + 5) → Bool) :
    FullBudget 1 (fun j => (p.point k slot fresh j : ℝ)) := by
  cases p with
  | dominant j heavy =>
    have he : (fun a => ((Prepared.dominant j heavy).point k slot fresh a : ℝ)) =
        PureBoundaryEquilibria.vertex 1 j := by
      funext a
      dsimp only [Prepared.point, PureBoundaryEquilibria.vertex]
      split_ifs <;> norm_num
    rw [he]
    exact PureBoundaryEquilibria.vertex_fullBudget 1 (by norm_num) j
  | grouped small => exact GeneralPaperEqualFiniteKernel.point_fullBudget v small k slot fresh

theorem Prepared.regret {n : ℕ} {v : RationalFieldSelector n} (p : Prepared v) (k : ℕ) :
    Supported 1 (p.law k) ∧
      regret v.values 1 (p.law k) (p.law k) ≤ (1 / (2 : ℝ) ^ k) / 32 := by
  cases p with
  | dominant j heavy =>
    have hh : (1 / 2 : ℝ) ≤ v.values.weight j := by
      change (1 / 2 : ℝ) ≤ (v.weight j : ℝ)
      have hh' : (((1 / 2 : ℚ) : ℝ)) ≤ (v.weight j : ℝ) := by exact_mod_cast heavy
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hh'
    have h := PureBoundaryEquilibria.dominant_vertex_equilibrium v.values 1 (by norm_num) j hh
    exact ⟨h.1, h.2.le.trans (by positivity)⟩
  | grouped small => exact GeneralPaperEqualFiniteKernel.regrets v small k

theorem Prepared.expected {n : ℕ} {v : RationalFieldSelector n} (p : Prepared v) (k : ℕ)
    (original : Values n) : expected original (p.law k) (p.law k) = 1 / 2 := by
  have h := expected_constant_sum original (p.law k) (p.law k)
  linarith only [h]

noncomputable def rounded {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) :
    RationalFieldSelector n :=
  GeneralPaperRoundedValuePerturbation.selector bits model W 128 k (by decide) values v hv

theorem distance {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) :
    GeneralPaperValuePerturbation.distance v.values (rounded bits model W k values v hv).values ≤
      (1 / (2 : ℝ) ^ k) / 64 := by
  have h := GeneralPaperRoundedValuePerturbation.distance bits model W 128 k (by decide) values v hv
  exact h.trans_eq (by ring)

theorem original_regret {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) :
    let p := prepare (rounded bits model W k values v hv)
    Supported 1 (p.law k) ∧
      regret v.values 1 (p.law k) (p.law k) ≤ 3 * (1 / (2 : ℝ) ^ k) / 32 := by
  dsimp only
  let p := prepare (rounded bits model W k values v hv)
  have hr := p.regret k
  have hd := distance bits model W k values v hv
  have ht := GeneralPaperValuePerturbation.regret_le_shift v.values
    (rounded bits model W k values v hv).values 1 (by norm_num) (p.law k) (p.law k)
  refine ⟨hr.1, ?_⟩
  have he : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ k := by positivity
  linarith only [hr.2, hd, ht, he]

theorem epsilon {n : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (eps : ℚ) (hp : 0 < eps) (hOne : eps < 1) :
    let k := (GeneralPaperDyadicAccuracy.prepare eps).exponent
    let p := prepare (rounded bits model W k values v hv)
    Supported 1 (p.law k) ∧ regret v.values 1 (p.law k) (p.law k) ≤ (eps : ℝ) ∧
      expected v.values (p.law k) (p.law k) = 1 / 2 ∧
      ∀ slot fresh, FullBudget 1 (fun j => (p.point k slot fresh j : ℝ)) := by
  dsimp only
  let k := (GeneralPaperDyadicAccuracy.prepare eps).exponent
  let p := prepare (rounded bits model W k values v hv)
  have h := original_regret bits model W k values v hv
  have he := (GeneralPaperDyadicAccuracy.accuracy_bounds eps hp hOne).2
  rw [GeneralPaperDyadicAccuracy.accuracy_power] at he
  have he' : (1 / (2 : ℝ) ^ k) ≤ (eps : ℝ) := by
    have hr : (((1 / (2 : ℚ) ^ (GeneralPaperDyadicAccuracy.prepare eps).exponent : ℚ) : ℝ)) ≤
        (eps : ℝ) := by exact_mod_cast he
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using hr
  have hep : (0 : ℝ) < eps := by exact_mod_cast hp
  refine ⟨h.1, ?_, p.expected k v.values, p.point_fullBudget k⟩
  linarith only [h.2, he', hep]

end Blotto.GeneralPaperEqualRoundedBoundary
