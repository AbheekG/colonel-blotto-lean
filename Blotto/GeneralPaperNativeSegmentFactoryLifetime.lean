import Blotto.GeneralPaperFixedSegmentFactoryLifetime

/-! Native pair/three factory lifetimes, including environment construction,
all compiler phases, the returned record and outer selector/control fields.
The phase tag witnesses the actual stored-size branch. Cached inputs and
fixed code are the caller's borrowed owner; all internal owners are covered. -/
namespace Blotto.GeneralPaperNativeSegmentFactoryLifetime
open GeneralPaperSegmentCompilerStorage (Bounds)
open GeneralPaperEncodedScalarStorage (natBits fields)
open GeneralPaperNativeSegmentCompilerLifetime (pairPrograms threePrograms)
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem pair_producer (B : ℚ) (model : RationalCostModel) (A : ℕ) :
    GeneralPaperFixedSegmentFactoryLifetime.actual model A (fun _ : Fin 1 => B) (pairPrograms B A) =
      GeneralPaperPairSegmentPreparation.run B model A := rfl

theorem three_producer (i : RationalThreeSpec) (model : RationalCostModel) (A : ℕ) :
    GeneralPaperFixedSegmentFactoryLifetime.actual model A (![i.B, i.a, i.d, i.c, i.p]) (threePrograms i A) =
      GeneralPaperThreeSegmentPreparation.run i model A := rfl

def pairWindow {m : ℕ} (i : RationalUniformGroupSpec m) (h2 : m = 2) (model : RationalCostModel)
    (A borrowed : ℕ) (phase : GeneralPaperFixedSegmentFactoryLifetime.Phase 2 9 1) : ℕ := by
  subst m
  exact GeneralPaperFixedSegmentFactoryLifetime.window model A (fun _ : Fin 1 => i.B) (pairPrograms i.B A) borrowed phase

def threeWindow {m : ℕ} (i : RationalUniformGroupSpec m) (h3 : m = 3) (model : RationalCostModel)
    (A borrowed : ℕ) (phase : GeneralPaperFixedSegmentFactoryLifetime.Phase 3 9 5) : ℕ := by
  subst m
  exact GeneralPaperFixedSegmentFactoryLifetime.window model A
    (![i.threeInput.B, i.threeInput.a, i.threeInput.d, i.threeInput.c, i.threeInput.p])
    (threePrograms i.threeInput A) borrowed phase

theorem pair_bound {m : ℕ} (i : RationalUniformGroupSpec m) (h2 : m = 2) (model : RationalCostModel)
    (A s borrowed : ℕ) (hs : 2 ≤ s) (h : i.FieldsHeight s)
    (phase : GeneralPaperFixedSegmentFactoryLifetime.Phase 2 9 1) :
    pairWindow i h2 model A borrowed phase ≤ GeneralPaperFixedSegmentFactoryLifetime.profile model A 2 9 1 s 0 1 borrowed := by
  subst m
  exact GeneralPaperFixedSegmentFactoryLifetime.all_phases model A (fun _ : Fin 1 => i.B) (pairPrograms i.B A)
    s 0 1 (fun _ => h.1) (GeneralPaperNativeSegmentCompilerLifetime.pair_bounds i.B A s hs h.1) borrowed phase

theorem three_bound {m : ℕ} (i : RationalUniformGroupSpec m) (h3 : m = 3) (model : RationalCostModel)
    (A s borrowed : ℕ) (hs : 2 ≤ s) (h : i.FieldsHeight s)
    (phase : GeneralPaperFixedSegmentFactoryLifetime.Phase 3 9 5) :
    threeWindow i h3 model A borrowed phase ≤ GeneralPaperFixedSegmentFactoryLifetime.profile model A 3 9 5 s 20 2048 borrowed := by
  subst m
  have hEnv := h.three_environment hs
  exact GeneralPaperFixedSegmentFactoryLifetime.all_phases model A _ (threePrograms i.threeInput A)
    s 20 2048 (by simpa only [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn] using hEnv)
    (GeneralPaperNativeSegmentCompilerLifetime.three_bounds i.threeInput A s hs hEnv) borrowed phase

inductive Phase (m : ℕ) where
  | pair (h2 : m = 2) (phase : GeneralPaperFixedSegmentFactoryLifetime.Phase 2 9 1)
  | triple (h3 : m = 3) (phase : GeneralPaperFixedSegmentFactoryLifetime.Phase 3 9 5)

def selectorFoot (A size work : ℕ) : ℕ :=
  let header := 64 * (A + binaryWordWidth (size + 1) + 1)
  fields A [size, work, header, work + header] + 128 * A

def selectorProfile (model : RationalCostModel) (A s : ℕ) : ℕ :=
  4 * (natBits (GeneralPaperUniformSegmentPreparation.bound model A s + 3) + A) + 160 * A

theorem selector_bound (model : RationalCostModel) (A s size work : ℕ) (hSize : size ≤ 3)
    (hWork : work ≤ GeneralPaperPairSegmentPreparation.bound model A s ∨
      work ≤ GeneralPaperThreeSegmentPreparation.bound model A s) : selectorFoot A size work ≤ selectorProfile model A s := by
  have hWidth : binaryWordWidth (size + 1) ≤ 3 := by
    have h := binaryWordWidth_mono (show size + 1 ≤ 4 by omega)
    have h4 : binaryWordWidth 4 = 3 := by decide
    omega
  have hHeader : 64 * (A + binaryWordWidth (size + 1) + 1) ≤ 256 * (A + 1) := by omega
  have hW : work + 64 * (A + binaryWordWidth (size + 1) + 1) ≤
      GeneralPaperUniformSegmentPreparation.bound model A s := by
    unfold GeneralPaperUniformSegmentPreparation.bound
    rcases hWork with h | h <;> omega
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A
    (GeneralPaperUniformSegmentPreparation.bound model A s + 3)
    [size, work, 64 * (A + binaryWordWidth (size + 1) + 1), work + 64 * (A + binaryWordWidth (size + 1) + 1)] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> omega)
  change fields A _ ≤ 4 * (natBits (GeneralPaperUniformSegmentPreparation.bound model A s + 3) + A) + 32 * A at hFields
  simp only [selectorFoot]
  unfold selectorProfile
  omega

def window {m : ℕ} (i : RationalUniformGroupSpec m) (size : ℕ) (hm : m = 2 ∨ m = 3)
    (model : RationalCostModel) (A borrowed : ℕ) : Phase m → ℕ
  | .pair h2 phase => pairWindow i h2 model A borrowed phase +
      selectorFoot A size (GeneralPaperUniformSegmentPreparation.pair i hm h2 model A).2
  | .triple h3 phase => threeWindow i h3 model A borrowed phase +
      selectorFoot A size (GeneralPaperUniformSegmentPreparation.triple i hm h3 model A).2

def profile (model : RationalCostModel) (A s borrowed : ℕ) : ℕ :=
  GeneralPaperFixedSegmentFactoryLifetime.profile model A 2 9 1 s 0 1 borrowed +
    GeneralPaperFixedSegmentFactoryLifetime.profile model A 3 9 5 s 20 2048 borrowed + selectorProfile model A s

theorem selected_branch {m : ℕ} (size : ℕ) (hSize : size = m) (phase : Phase m) :
    match phase with | .pair _ _ => size = 2 | .triple _ _ => size ≠ 2 := by
  cases phase with
  | pair h2 _ => omega
  | triple h3 _ => omega

theorem bounded {m : ℕ} (i : RationalUniformGroupSpec m) (size : ℕ) (hSize : size = m) (hm : m = 2 ∨ m = 3)
    (model : RationalCostModel) (A s borrowed : ℕ) (hs : 2 ≤ s) (h : i.FieldsHeight s) (phase : Phase m) :
    window i size hm model A borrowed phase ≤ profile model A s borrowed := by
  have hSize3 : size ≤ 3 := by rcases hm with h | h <;> omega
  cases phase with
  | pair h2 phase =>
    have hFactory := pair_bound i h2 model A s borrowed hs h phase
    have hSelect := selector_bound model A s size (GeneralPaperUniformSegmentPreparation.pair i hm h2 model A).2 hSize3
      (Or.inl (GeneralPaperUniformSegmentPreparation.pair_work i hm h2 model A s hs h))
    simp only [window, profile]
    omega
  | triple h3 phase =>
    have hFactory := three_bound i h3 model A s borrowed hs h phase
    have hSelect := selector_bound model A s size (GeneralPaperUniformSegmentPreparation.triple i hm h3 model A).2 hSize3
      (Or.inr (GeneralPaperUniformSegmentPreparation.triple_work i hm h3 model A s hs h))
    simp only [window, profile]
    omega

theorem native {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded bits model W exponent values v hv).weight j ≤ 1)
    (p : RationalTerminalPacking (GeneralPaperEqualFiniteKernel.terminal
      (GeneralPaperEqualNativeSampler.rounded bits model W exponent values v hv) small))
    (borrowed : ℕ) (phase : Phase (GeneralPaperEqualFiniteKernel.terminal
      (GeneralPaperEqualNativeSampler.rounded bits model W exponent values v hv) small).groups.length) :
    window (p.uniformSpec (GeneralPaperEqualFiniteKernel.no_fraction _ small)) p.groups.data.size
      (GeneralPaperEqualFiniteKernel.terminal _ small).groups_count model A borrowed phase ≤
      profile model A (GeneralPaperEqualNativeSampler.fieldHeight n exponent) borrowed := by
  apply bounded _ _ p.groups.size
  · unfold GeneralPaperEqualNativeSampler.fieldHeight
    omega
  · exact GeneralPaperEqualNativeSegmentPreparation.fields_height bits model W exponent values v hv small p

end Blotto.GeneralPaperNativeSegmentFactoryLifetime
