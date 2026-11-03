import Blotto.ResourceUpdate
import Blotto.BinaryMixture

/-! Finite conditional rounding lotteries. Every node has an explicit
probability and both child outcomes; the tree is a mathematical semantics,
not a claimed linear-time representation of the global sampler. -/

namespace Blotto
open MeasureTheory Set Filter
open scoped BigOperators

inductive RoundingTree (n : ℕ) where
  | leaf (resource : Allocation n)
  | fork (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (upper lower : RoundingTree n)

namespace RoundingTree

def height {n : ℕ} : RoundingTree n → ℕ
  | .leaf _ => 0
  | .fork _ _ a b => 1 + max a.height b.height

def ForLeaves {n : ℕ} (P : Allocation n → Prop) : RoundingTree n → Prop
  | .leaf r => P r
  | .fork _ _ a b => a.ForLeaves P ∧ b.ForLeaves P

noncomputable def average {n : ℕ} : RoundingTree n → Allocation n
  | .leaf r => r
  | .fork p _ a b => fun j => p * a.average j + (1 - p) * b.average j

noncomputable def eval {n m : ℕ} (T : RoundingTree n) (leafLaw : Allocation n → Mixed m) : Mixed m :=
  match T with
  | .leaf r => leafLaw r
  | .fork p hp a b => binaryLaw p hp (a.eval leafLaw) (b.eval leafLaw)

theorem forLeaves_mono {n : ℕ} {P Q : Allocation n → Prop} (T : RoundingTree n)
    (h : ∀ r, P r → Q r) (hT : T.ForLeaves P) : T.ForLeaves Q := by
  induction T with
  | leaf r => exact h r hT
  | fork p hp a b ha hb => exact ⟨ha hT.1, hb hT.2⟩

theorem average_inBox {n : ℕ} (T : RoundingTree n) (length : Allocation n)
    (hT : T.ForLeaves (InBox length)) : InBox length T.average := by
  induction T with
  | leaf r => exact hT
  | fork p hp a b ha hb =>
    have hA := ha hT.1
    have hB := hb hT.2
    intro j
    constructor
    · exact add_nonneg (mul_nonneg hp.1 (hA j).1) (mul_nonneg (sub_nonneg.mpr hp.2) (hB j).1)
    · have h1 := mul_le_mul_of_nonneg_left (hA j).2 hp.1
      have h2 := mul_le_mul_of_nonneg_left (hB j).2 (sub_nonneg.mpr hp.2)
      change p * a.average j + (1 - p) * b.average j ≤ length j
      nlinarith

theorem eval_fullBudget {n m : ℕ} (T : RoundingTree n) (leafLaw : Allocation n → Mixed m)
    (B : ℝ) (hT : T.ForLeaves (fun r => ∀ᵐ x ∂(leafLaw r : Measure (Allocation m)), FullBudget B x)) :
    ∀ᵐ x ∂(T.eval leafLaw : Measure (Allocation m)), FullBudget B x := by
  induction T with
  | leaf r => exact hT
  | fork p hp a b ha hb => exact binaryLaw_fullBudget p hp _ _ (ha hT.1) (hb hT.2)

theorem eval_inBox {n m : ℕ} (T : RoundingTree n) (leafLaw : Allocation n → Mixed m)
    (length : Allocation m) (hT : T.ForLeaves (fun r => ∀ᵐ x ∂(leafLaw r : Measure (Allocation m)), InBox length x)) :
    ∀ᵐ x ∂(T.eval leafLaw : Measure (Allocation m)), InBox length x := by
  induction T with
  | leaf r => exact hT
  | fork p hp a b ha hb =>
    have hw : ∀ i : Fin 2, 0 ≤ (![p, 1 - p] : Fin 2 → ℝ) i := by
      intro i
      fin_cases i
      · exact hp.1
      · exact sub_nonneg.mpr hp.2
    have hs : ∑ i : Fin 2, (![p, 1 - p] : Fin 2 → ℝ) i = 1 := by simp [Fin.sum_univ_succ]
    exact probabilityMixture_ae ![p, 1 - p] ![a.eval leafLaw, b.eval leafLaw] hw hs (by
      intro i
      fin_cases i
      · exact ha hT.1
      · exact hb hT.2)

/-- Follow binary outcomes along one path; no unused random inputs are read. -/
noncomputable def traceLeaf {n : ℕ} (T : RoundingTree n) (choice : ℕ → Bool) : Allocation n :=
  match T with
  | .leaf r => r
  | .fork _ _ a b => if choice 0 then a.traceLeaf (fun k => choice (k + 1))
      else b.traceLeaf (fun k => choice (k + 1))

theorem trace_forLeaves {n : ℕ} (T : RoundingTree n) (P : Allocation n → Prop)
    (hT : T.ForLeaves P) (choice : ℕ → Bool) : P (T.traceLeaf choice) := by
  induction T generalizing choice with
  | leaf r => exact hT
  | fork p hp a b ha hb =>
    unfold traceLeaf
    split_ifs
    · exact ha hT.1 _
    · exact hb hT.2 _

end RoundingTree
end Blotto
