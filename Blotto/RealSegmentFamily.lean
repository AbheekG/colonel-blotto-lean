import Blotto.RealCategoricalFamily
import Blotto.RealSegmentFlat
import Blotto.ParameterLaw

/-! Measurable parameter-dependent segment tables are realized by the same
cached categorical runtime and independent interpolation used for fixed tables. -/

namespace Blotto.SegmentLottery
open MeasureTheory

theorem realSampleFlat_measurable_family {θ : Type*} [MeasurableSpace θ] {n k : ℕ}
    (l : θ → SegmentLottery n k) (fallback : Fin k)
    (hw : ∀ j, Measurable (fun z => (l z).weight j))
    (hP : ∀ j, Measurable (fun z => (l z).P j)) (hQ : ∀ j, Measurable (fun z => (l z).Q j))
    (seed : θ → Fin ((k - 1) + 1) → ℝ) (hs : Measurable seed) :
    Measurable (fun z => (l z).realSampleFlat fallback (seed z)) := by
  rw [show (fun z => (l z).realSampleFlat fallback (seed z)) = fun z =>
    (l z).point (realCategorical (l z).weight (l z).nonnegative fallback (Fin.tail (seed z))) (seed z 0)
    from funext (fun z => (l z).realSampleFlat_refines fallback (seed z))]
  have hTail : Measurable (fun z => Fin.tail (seed z)) := by
    apply Measurable.of_eval
    intro j
    exact (measurable_pi_apply j.succ).comp hs
  have hChoice := realCategorical_measurable_family (fun z => (l z).weight)
    (fun z => (l z).nonnegative) fallback (fun z => Fin.tail (seed z)) hw hTail
  have hPF : Measurable (fun z : θ × Fin k => (l z.1).P z.2) :=
    measurable_from_prod_countable_left hP
  have hQF : Measurable (fun z : θ × Fin k => (l z.1).Q z.2) :=
    measurable_from_prod_countable_left hQ
  have hPS := hPF.comp (measurable_id.prodMk hChoice)
  have hQS := hQF.comp (measurable_id.prodMk hChoice)
  have hScalar := (measurable_pi_apply 0).comp hs
  apply Measurable.of_eval
  intro j
  change Measurable (fun z => (1 - seed z 0) *
    (l z).P (realCategorical (l z).weight (l z).nonnegative fallback (Fin.tail (seed z))) j +
    seed z 0 * (l z).Q (realCategorical (l z).weight (l z).nonnegative fallback (Fin.tail (seed z))) j)
  exact ((measurable_const.sub hScalar).mul ((measurable_pi_apply j).comp hPS)).add
    (hScalar.mul ((measurable_pi_apply j).comp hQS))

theorem realSampleFlat_measurable_joint {θ : Type*} [MeasurableSpace θ] {n k : ℕ}
    (l : θ → SegmentLottery n k) (fallback : Fin k)
    (hw : ∀ j, Measurable (fun z => (l z).weight j))
    (hP : ∀ j, Measurable (fun z => (l z).P j)) (hQ : ∀ j, Measurable (fun z => (l z).Q j)) :
    Measurable (fun z : θ × (Fin ((k - 1) + 1) → ℝ) => (l z.1).realSampleFlat fallback z.2) := by
  exact realSampleFlat_measurable_family (θ := θ × (Fin ((k - 1) + 1) → ℝ))
    (fun z => l z.1) fallback (fun j => (hw j).comp measurable_fst)
    (fun j => (hP j).comp measurable_fst) (fun j => (hQ j).comp measurable_fst) Prod.snd measurable_snd

end Blotto.SegmentLottery
