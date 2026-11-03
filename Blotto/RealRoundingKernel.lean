import Blotto.RealUniformProduct
import Blotto.RealRoundingSource

/-! A finite rounding source followed by a fresh independent leaf sampler
realizes its existing conditional whole law. The tree is a proof reference
for an indexed source runtime, rather than a production representation. -/

namespace Blotto
open MeasureTheory

namespace RealChoiceTree

theorem output_leaf {α : Type*} (x : α) (C : ℕ) (fallback : α) (seed : Fin C → ℝ) :
    (leaf x).output C fallback seed = x := by cases C <;> rfl

end RealChoiceTree
namespace RoundingTree

noncomputable def realKernel {n m : ℕ} {S : Type*} (T : RoundingTree n) (C : ℕ)
    (fallback : Allocation n) (sample : Allocation n → S → Allocation m)
    (z : (Fin C → ℝ) × S) : Allocation m :=
  sample (T.realChoice.output C fallback z.1) z.2

theorem realKernel_leaf {n m : ℕ} {S : Type*} (r : Allocation n) (C : ℕ)
    (fallback : Allocation n) (sample : Allocation n → S → Allocation m) :
    (leaf r).realKernel C fallback sample = sample r ∘ Prod.snd := by
  funext z
  unfold realKernel
  rw [realChoice, RealChoiceTree.output_leaf]
  rfl

theorem realKernel_fork_succ {n m : ℕ} {S : Type*} (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (upper lower : RoundingTree n) (C : ℕ) (fallback : Allocation n)
    (sample : Allocation n → S → Allocation m) (z : (Fin (C + 1) → ℝ) × S) :
    (fork p hp upper lower).realKernel (C + 1) fallback sample z =
      if z.1 0 ≤ p then upper.realKernel C fallback sample (Fin.tail z.1, z.2)
      else lower.realKernel C fallback sample (Fin.tail z.1, z.2) := by
  unfold realKernel
  rw [realChoice, RealChoiceTree.output_fork_succ]
  unfold RealThresholdChoice.sample
  split_ifs <;> rfl

theorem realKernel_measurable {n m : ℕ} {S : Type*} [MeasurableSpace S]
    (T : RoundingTree n) (C : ℕ) (fallback : Allocation n) (sample : Allocation n → S → Allocation m)
    (hMeas : T.ForLeaves (fun r => Measurable (sample r))) (hC : T.height ≤ C) :
    Measurable (T.realKernel C fallback sample) := by
  induction T generalizing C with
  | leaf r =>
    rw [realKernel_leaf]
    exact hMeas.comp measurable_snd
  | fork p hp upper lower ihUpper ihLower =>
    cases C with
    | zero => simp [height] at hC
    | succ C =>
      have hUpper : upper.height ≤ C := by simp only [height] at hC; omega
      have hLower : lower.height ≤ C := by simp only [height] at hC; omega
      have hA := ihUpper C hMeas.1 hUpper
      have hB := ihLower C hMeas.2 hLower
      have hEq : (fork p hp upper lower).realKernel (C + 1) fallback sample =
          RealIndependentChoice.sample p (upper.realKernel C fallback sample) (lower.realKernel C fallback sample) ∘
            RealUniformInputs.productSplit C := by
        funext z
        exact realKernel_fork_succ p hp upper lower C fallback sample z
      rw [hEq]
      exact (RealIndependentChoice.measurable_sample p _ _ hA hB).comp (RealUniformInputs.productSplit_measurable C)

theorem realKernel_law {n m : ℕ} {S : Type*} [MeasurableSpace S]
    (T : RoundingTree n) (C : ℕ) (fallback : Allocation n) (ν : ProbabilityMeasure S)
    (sample : Allocation n → S → Allocation m) (leafLaw : Allocation n → Mixed m)
    (hMeas : T.ForLeaves (fun r => Measurable (sample r)))
    (hLaw : T.ForLeaves (fun r => Measure.map (sample r) (ν : Measure S) = (leafLaw r : Measure (Allocation m))))
    (hC : T.height ≤ C) :
    Measure.map (T.realKernel C fallback sample) ((RealUniformInputs.law C : Measure (Fin C → ℝ)).prod (ν : Measure S)) =
      (T.eval leafLaw : Measure (Allocation m)) := by
  induction T generalizing C with
  | leaf r =>
    rw [realKernel_leaf, ← Measure.map_map hMeas measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]
    exact hLaw
  | fork p hp upper lower ihUpper ihLower =>
    cases C with
    | zero => simp [height] at hC
    | succ C =>
      have hUpper : upper.height ≤ C := by simp only [height] at hC; omega
      have hLower : lower.height ≤ C := by simp only [height] at hC; omega
      have hA := upper.realKernel_measurable C fallback sample hMeas.1 hUpper
      have hB := lower.realKernel_measurable C fallback sample hMeas.2 hLower
      rw [RealUniformInputs.map_product_succ C (ν : Measure S) _
        ((fork p hp upper lower).realKernel_measurable (C + 1) fallback sample hMeas hC)]
      have hEq : (fork p hp upper lower).realKernel (C + 1) fallback sample ∘ RealUniformInputs.productJoin C =
          RealIndependentChoice.sample p (upper.realKernel C fallback sample) (lower.realKernel C fallback sample) := by
        funext z
        rw [Function.comp_apply, realKernel_fork_succ]
        simp only [RealUniformInputs.productJoin, RealUniformInputs.join, Fin.cons_zero, Fin.tail_cons]
        rfl
      rw [hEq]
      change Measure.map (RealIndependentChoice.sample p (upper.realKernel C fallback sample) (lower.realKernel C fallback sample))
        ((unitUniform : Measure ℝ).prod
          (RealUniformInputs.productLaw (RealUniformInputs.law C) ν : Measure ((Fin C → ℝ) × S))) = _
      rw [RealIndependentChoice.map_product p hp (RealUniformInputs.productLaw (RealUniformInputs.law C) ν) _ _ hA hB]
      change ENNReal.ofReal p • Measure.map (upper.realKernel C fallback sample)
        ((RealUniformInputs.law C : Measure (Fin C → ℝ)).prod (ν : Measure S)) +
        ENNReal.ofReal (1 - p) • Measure.map (lower.realKernel C fallback sample)
          ((RealUniformInputs.law C : Measure (Fin C → ℝ)).prod (ν : Measure S)) = _
      rw [ihUpper C hMeas.1 hLaw.1 hUpper, ihLower C hMeas.2 hLaw.2 hLower]
      exact (binaryLaw_measure p hp (upper.eval leafLaw) (lower.eval leafLaw)).symm

end RoundingTree
end Blotto
