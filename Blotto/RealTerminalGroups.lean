import Blotto.RealUniformGroups
import Blotto.RealMixedGroups
import Blotto.RealCachedGroupSpecs
import Blotto.TerminalLottoLaw

/-! The grouped terminal draw is emitted into a native array using cached
routes. Its allocation view equals the retained proportional split exactly. -/

namespace Blotto.TerminalLotto
open MeasureTheory

noncomputable def realUniformArray {n : ℕ} (i : TerminalLotto n)
    (h : ∀ j, ¬Fractional i.length i.resource j) (seed : RealFourSeed) : FixedArrayTable n ℝ :=
  let output := (RealTerminalPacking.prepare i).prepareOutput
  output.emit ((output.uniformSpec h).realSample i.groups_count seed)

noncomputable def realUniformSample {n : ℕ} (i : TerminalLotto n)
    (h : ∀ j, ¬Fractional i.length i.resource j) (seed : RealFourSeed) : Allocation n :=
  (i.realUniformArray h seed).read

theorem realUniformSample_eq_split {n : ℕ} (i : TerminalLotto n)
    (h : ∀ j, ¬Fractional i.length i.resource j) (seed : RealFourSeed) :
    i.realUniformSample h seed = i.partition.split ((i.uniformSpec h).realSample i.groups_count seed) := by
  let output := (RealTerminalPacking.prepare i).prepareOutput
  change (output.emit ((output.uniformSpec h).realSample i.groups_count seed)).read = _
  rw [output.emit_allocation, output.uniformSpec_eq]

theorem realUniformSample_measurable {n : ℕ} (i : TerminalLotto n)
    (h : ∀ j, ¬Fractional i.length i.resource j) : Measurable (i.realUniformSample h) := by
  have hEq : i.realUniformSample h = i.partition.split ∘ (i.uniformSpec h).realSample i.groups_count :=
    funext (i.realUniformSample_eq_split h)
  rw [hEq]
  exact i.partition.measurable_split.comp ((i.uniformSpec h).realSample_measurable i.groups_count)

theorem realUniformSample_law {n : ℕ} (i : TerminalLotto n)
    (h : ∀ j, ¬Fractional i.length i.resource j) :
    Measure.map (i.realUniformSample h) (FourInput.realInputLaw : Measure RealFourSeed) =
      (i.uniformLaw h : Measure (Allocation n)) := by
  have hEq : i.realUniformSample h = i.partition.split ∘ (i.uniformSpec h).realSample i.groups_count :=
    funext (i.realUniformSample_eq_split h)
  rw [hEq, ← Measure.map_map i.partition.measurable_split ((i.uniformSpec h).realSample_measurable i.groups_count),
    (i.uniformSpec h).realSample_law i.groups_count]
  rfl

theorem realUniformSample_fullBudget {n : ℕ} (i : TerminalLotto n)
    (h : ∀ j, ¬Fractional i.length i.resource j) (seed : RealFourSeed) (hs : realGroupSeedValid seed) :
    FullBudget i.B (i.realUniformSample h seed) := by
  rw [i.realUniformSample_eq_split h seed]
  exact i.partition.split_fullBudget ((i.uniformSpec h).realSample_fullBudget i.groups_count seed hs)

noncomputable def realMixedArray {n : ℕ} (i : TerminalLotto n) (pivot : Fin n)
    (hp : Fractional i.length i.resource pivot) (seed : RealFourSeed) : FixedArrayTable n ℝ :=
  let output := (RealTerminalPacking.prepare i).prepareOutput
  output.emitMixed pivot ((output.mixedSpec pivot hp).realSample i.groups_count seed)

noncomputable def realMixedSample {n : ℕ} (i : TerminalLotto n) (pivot : Fin n)
    (hp : Fractional i.length i.resource pivot) (seed : RealFourSeed) : Allocation n :=
  (i.realMixedArray pivot hp seed).read

theorem realMixedSample_eq_split {n : ℕ} (i : TerminalLotto n) (pivot : Fin n)
    (hp : Fractional i.length i.resource pivot) (seed : RealFourSeed) :
    i.realMixedSample pivot hp seed = i.partition.splitMixed pivot ((i.mixedSpec pivot hp).realSample i.groups_count seed) := by
  let output := (RealTerminalPacking.prepare i).prepareOutput
  change (output.emitMixed pivot ((output.mixedSpec pivot hp).realSample i.groups_count seed)).read = _
  rw [output.emitMixed_allocation, output.mixedSpec_eq]

theorem realMixedSample_measurable {n : ℕ} (i : TerminalLotto n) (pivot : Fin n)
    (hp : Fractional i.length i.resource pivot) : Measurable (i.realMixedSample pivot hp) := by
  have hEq : i.realMixedSample pivot hp = i.partition.splitMixed pivot ∘ (i.mixedSpec pivot hp).realSample i.groups_count :=
    funext (i.realMixedSample_eq_split pivot hp)
  rw [hEq]
  exact (i.partition.measurable_splitMixed pivot).comp ((i.mixedSpec pivot hp).realSample_measurable i.groups_count)

theorem realMixedSample_law {n : ℕ} (i : TerminalLotto n) (pivot : Fin n)
    (hp : Fractional i.length i.resource pivot) :
    Measure.map (i.realMixedSample pivot hp) (FourInput.realInputLaw : Measure RealFourSeed) =
      (i.mixedLaw pivot hp : Measure (Allocation n)) := by
  have hEq : i.realMixedSample pivot hp = i.partition.splitMixed pivot ∘ (i.mixedSpec pivot hp).realSample i.groups_count :=
    funext (i.realMixedSample_eq_split pivot hp)
  rw [hEq, ← Measure.map_map (i.partition.measurable_splitMixed pivot) ((i.mixedSpec pivot hp).realSample_measurable i.groups_count),
    (i.mixedSpec pivot hp).realSample_law i.groups_count]
  rfl

theorem realMixedSample_fullBudget {n : ℕ} (i : TerminalLotto n) (pivot : Fin n)
    (hp : Fractional i.length i.resource pivot) (seed : RealFourSeed) (hs : realGroupSeedValid seed) :
    FullBudget i.B (i.realMixedSample pivot hp seed) := by
  rw [i.realMixedSample_eq_split pivot hp seed]
  exact i.partition.splitMixed_fullBudget pivot ((i.mixedSpec pivot hp).realSample_fullBudget i.groups_count seed hs)

end Blotto.TerminalLotto
