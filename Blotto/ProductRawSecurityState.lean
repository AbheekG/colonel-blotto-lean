import Blotto.ProductSecurityTrainer
import Blotto.PreparedGibbsMean

/-! Rational whole-row observations drive the same stored field updates as the
finite labelled trainer. Encoding may identify duplicate bid rows. Preparation
uses the actual positive updated fields and the original hard budgets. -/

namespace Blotto
open scoped BigOperators Classical
namespace ProductSecurityTrainer

abbrev RawObservation (m : ℕ) := PreparedRationalTransition.Observation m

def rawSelected {m : ℕ} (_history : List (RawObservation m)) (x : RawObservation m) : Fin m := x.2.2

def rawLossA {m : ℕ} (c : ProductSecurityTrainer m) (_history : List (RawObservation m))
    (x : RawObservation m) (code : Fin (c.sizesA x.2.2)) : ℚ :=
  SparseMW.rationalShare (x.2.1 x.2.2) (c.bidsA x.2.2 code)

def rawLossB {m : ℕ} (c : ProductSecurityTrainer m) (_history : List (RawObservation m))
    (x : RawObservation m) (code : Fin (c.sizesB x.2.2)) : ℚ :=
  SparseMW.rationalShare (x.1 x.2.2) (c.bidsB x.2.2 code)

def rawFieldsA {m : ℕ} (c : ProductSecurityTrainer m) :
    List (RawObservation m) → (j : Fin m) → Fin (c.sizesA j) → ℚ
  | [] => fun _ _ => 1
  | x :: history =>
    let old := c.rawFieldsA history
    Function.update old x.2.2
      (fun code => SparseMW.storedUpdate (old x.2.2 code) c.eta (c.rawLossA history x code) c.theta)

def rawFieldsB {m : ℕ} (c : ProductSecurityTrainer m) :
    List (RawObservation m) → (j : Fin m) → Fin (c.sizesB j) → ℚ
  | [] => fun _ _ => 1
  | x :: history =>
    let old := c.rawFieldsB history
    Function.update old x.2.2
      (fun code => SparseMW.storedUpdate (old x.2.2 code) c.eta (c.rawLossB history x code) c.theta)

theorem rawLossA_unit {m : ℕ} (c : ProductSecurityTrainer m) :
    ∀ history x code, 0 ≤ c.rawLossA history x code ∧ c.rawLossA history x code ≤ 1 :=
  fun _ _ _ => SparseMW.rationalShare_unit _ _

theorem rawLossB_unit {m : ℕ} (c : ProductSecurityTrainer m) :
    ∀ history x code, 0 ≤ c.rawLossB history x code ∧ c.rawLossB history x code ≤ 1 :=
  fun _ _ _ => SparseMW.rationalShare_unit _ _

theorem rawFieldsA_positive {m : ℕ} (c : ProductSecurityTrainer m) (history : List (RawObservation m)) :
    ∀ j code, 0 < c.rawFieldsA history j code := by
  induction history with
  | nil => intro j code; norm_num [rawFieldsA]
  | cons x history ih =>
    intro j code
    by_cases hj : j = x.2.2
    · subst j
      simp only [rawFieldsA, Function.update_self]
      exact SparseMW.storedUpdate_positive _ _ _ _ (ih _ _)
        ⟨mul_nonneg c.eta_unit.1.le (c.rawLossA_unit history x code).1,
          (mul_le_of_le_one_right c.eta_unit.1.le (c.rawLossA_unit history x code).2).trans c.eta_unit.2⟩ c.theta_unit
    · simp only [rawFieldsA, Function.update_of_ne hj]
      exact ih j code

theorem rawFieldsB_positive {m : ℕ} (c : ProductSecurityTrainer m) (history : List (RawObservation m)) :
    ∀ j code, 0 < c.rawFieldsB history j code := by
  induction history with
  | nil => intro j code; norm_num [rawFieldsB]
  | cons x history ih =>
    intro j code
    by_cases hj : j = x.2.2
    · subst j
      simp only [rawFieldsB, Function.update_self]
      exact SparseMW.storedUpdate_positive _ _ _ _ (ih _ _)
        ⟨mul_nonneg c.eta_unit.1.le (c.rawLossB_unit history x code).1,
          (mul_le_of_le_one_right c.eta_unit.1.le (c.rawLossB_unit history x code).2).trans c.eta_unit.2⟩ c.theta_unit
    · simp only [rawFieldsB, Function.update_of_ne hj]
      exact ih j code

noncomputable def encodeObservation {m : ℕ} (c : ProductSecurityTrainer m)
    (x : Fin c.observations) : RawObservation m :=
  (fun j => c.bidsA j (c.codeA (c.observed x).1 j),
    fun j => c.bidsB j (c.codeB (c.observed x).2.1 j), (c.observed x).2.2)

theorem rawFieldsA_encoded {m : ℕ} (c : ProductSecurityTrainer m) (history : List (Fin c.observations)) :
    c.rawFieldsA (history.map c.encodeObservation) = c.fieldsA history := by
  induction history with
  | nil => rfl
  | cons x history ih =>
    simp only [List.map_cons, rawFieldsA, fieldsA, SparseMW.roundedFieldHistory]
    change Function.update (c.rawFieldsA (history.map c.encodeObservation)) (c.selected history x)
      (fun code => SparseMW.storedUpdate (c.rawFieldsA (history.map c.encodeObservation) (c.selected history x) code)
        c.eta (c.localLossA history x code) c.theta) = _
    rw [ih]
    rfl

theorem rawFieldsB_encoded {m : ℕ} (c : ProductSecurityTrainer m) (history : List (Fin c.observations)) :
    c.rawFieldsB (history.map c.encodeObservation) = c.fieldsB history := by
  induction history with
  | nil => rfl
  | cons x history ih =>
    simp only [List.map_cons, rawFieldsB, fieldsB, SparseMW.roundedFieldHistory]
    change Function.update (c.rawFieldsB (history.map c.encodeObservation)) (c.selected history x)
      (fun code => SparseMW.storedUpdate (c.rawFieldsB (history.map c.encodeObservation) (c.selected history x) code)
        c.eta (c.localLossB history x code) c.theta) = _
    rw [ih]
    rfl

def rawPreparedA {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (history : List (RawObservation (n + 1))) :
    PreparedProductSampler (n + 1) :=
  ProductArrayTree.prepareSampler n c.sizesA c.bidsA (c.rawFieldsA history) c.bidsA_nonnegative
    (c.rawFieldsA_positive history) c.budgetA c.fallbackA c.fallbackA_feasible

def rawPreparedB {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (history : List (RawObservation (n + 1))) :
    PreparedProductSampler (n + 1) :=
  ProductArrayTree.prepareSampler n c.sizesB c.bidsB (c.rawFieldsB history) c.bidsB_nonnegative
    (c.rawFieldsB_positive history) c.budgetB c.fallbackB c.fallbackB_feasible

theorem rawPreparedA_budget {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (history : List (RawObservation (n + 1))) :
    (c.rawPreparedA history).budget = c.budgetA := rfl

theorem rawPreparedB_budget {n : ℕ} (c : ProductSecurityTrainer (n + 1)) (history : List (RawObservation (n + 1))) :
    (c.rawPreparedB history).budget = c.budgetB := rfl

theorem rawPreparedA_encoded_mean {n : ℕ} (c : ProductSecurityTrainer (n + 1))
    (history : List (Fin c.observations)) (test : (Fin (n + 1) → ℚ) → ℝ) :
    (c.rawPreparedA (history.map c.encodeObservation)).rationalTargetKernel.mean test =
      ∑ i, (c.lawA history).realWeight i * test ((c.lawA history).row i) := by
  unfold rawPreparedA
  rw [ProductArrayTree.prepareSampler_rational_target_mean]
  simp only [rawFieldsA_encoded]
  rfl

theorem rawPreparedB_encoded_mean {n : ℕ} (c : ProductSecurityTrainer (n + 1))
    (history : List (Fin c.observations)) (test : (Fin (n + 1) → ℚ) → ℝ) :
    (c.rawPreparedB (history.map c.encodeObservation)).rationalTargetKernel.mean test =
      ∑ i, (c.lawB history).realWeight i * test ((c.lawB history).row i) := by
  unfold rawPreparedB
  rw [ProductArrayTree.prepareSampler_rational_target_mean]
  simp only [rawFieldsB_encoded]
  rfl

end ProductSecurityTrainer
end Blotto
