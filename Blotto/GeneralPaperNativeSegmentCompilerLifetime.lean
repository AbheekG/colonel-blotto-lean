import Blotto.GeneralPaperSegmentCompilerLifetime

/-! Actual fixed pair/three compiler phases, selected by retained group-array
size. The same prepared environments/programs as the executed factory are
used; all native height premises come from the positive-rounded fields. -/
namespace Blotto.GeneralPaperNativeSegmentCompilerLifetime
open GeneralPaperSegmentCompilerStorage (Bounds)
open GeneralPaperSegmentCompilerLifetime (Phase)
set_option autoImplicit false
set_option maxHeartbeats 1600000

def pairPrograms (B : ℚ) (A : ℕ) :=
  GeneralPaperPairSegmentPreparation.programs B (GeneralPaperPairSegmentPreparation.environment B A).1
    (by intro j; rw [GeneralPaperPairSegmentPreparation.environment_data, FixedArrayTable.read_ofFn])

def threePrograms (i : RationalThreeSpec) (A : ℕ) :=
  GeneralPaperThreeSegmentPreparation.programs i (GeneralPaperThreeSegmentPreparation.environment i A).1
    (GeneralPaperThreeSegmentPreparation.environment_data i A)

theorem pair_bounds (B : ℚ) (A s : ℕ) (hs : 2 ≤ s) (hB : RationalHeight B s) :
    Bounds (pairPrograms B A) s 0 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [GeneralPaperPairSegmentPreparation.environment_data, FixedArrayTable.read_ofFn]
    exact hB
  · intro i
    change RationalHeight (if i.val = 0 then (1 : ℚ) else 0) s
    split_ifs <;> exact (show RationalHeight (_ : ℚ) 2 by norm_num [RationalHeight]).mono hs
  · intro i j
    fin_cases j
    · exact (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
    · exact True.intro
  · intro i j
    fin_cases j
    · exact True.intro
    · exact (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  · intro i; exact le_rfl
  · intro i j; fin_cases j <;> exact le_rfl
  · intro i j; fin_cases j <;> exact le_rfl
  · intro i; exact le_rfl
  · intro i j; fin_cases j <;> exact le_rfl
  · intro i j; fin_cases j <;> exact le_rfl

theorem three_bounds (i : RationalThreeSpec) (A s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((RationalThreeSpecCode.environment i).read j) s) :
    Bounds (threePrograms i A) s 20 2048 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [GeneralPaperThreeSegmentPreparation.environment_data]
    exact hEnv j
  · exact fun slot => RationalExpression.LiteralHeights_mono _ hs (GeneralPaperThreeStaticPrograms.weight_literals slot)
  · exact fun slot j => RationalExpression.LiteralHeights_mono _ hs (GeneralPaperThreeStaticPrograms.left_literals slot j)
  · exact fun slot j => RationalExpression.LiteralHeights_mono _ hs (GeneralPaperThreeStaticPrograms.right_literals slot j)
  · exact GeneralPaperThreeStaticPrograms.weight_depth
  · exact GeneralPaperThreeStaticPrograms.left_depth
  · exact GeneralPaperThreeStaticPrograms.right_depth
  · exact GeneralPaperThreeStaticPrograms.weight_operations
  · exact GeneralPaperThreeStaticPrograms.left_operations
  · exact GeneralPaperThreeStaticPrograms.right_operations

def pairWindow {m : ℕ} (i : RationalUniformGroupSpec m) (h2 : m = 2) (model : RationalCostModel)
    (A borrowed : ℕ) (phase : Phase m 9) : ℕ := by
  subst m
  exact GeneralPaperSegmentCompilerLifetime.window model A (GeneralPaperPairSegmentPreparation.environment i.B A).1
    (pairPrograms i.B A) borrowed phase

def threeWindow {m : ℕ} (i : RationalUniformGroupSpec m) (h3 : m = 3) (model : RationalCostModel)
    (A borrowed : ℕ) (phase : Phase m 9) : ℕ := by
  subst m
  exact GeneralPaperSegmentCompilerLifetime.window model A (GeneralPaperThreeSegmentPreparation.environment i.threeInput A).1
    (threePrograms i.threeInput A) borrowed phase

def window {m : ℕ} (i : RationalUniformGroupSpec m) (size : ℕ) (hSize : size = m) (hm : m = 2 ∨ m = 3)
    (model : RationalCostModel) (A borrowed : ℕ) (phase : Phase m 9) : ℕ :=
  if h2 : size = 2 then pairWindow i (hSize.symm.trans h2) model A borrowed phase
  else threeWindow i (hm.resolve_left (fun h => h2 (hSize.trans h))) model A borrowed phase

def profile (model : RationalCostModel) (A s borrowed : ℕ) : ℕ :=
  GeneralPaperSegmentCompilerLifetime.profile model A 2 9 1 s 0 1 borrowed +
    GeneralPaperSegmentCompilerLifetime.profile model A 3 9 5 s 20 2048 borrowed

theorem pair_bounded {m : ℕ} (i : RationalUniformGroupSpec m) (h2 : m = 2) (model : RationalCostModel)
    (A s borrowed : ℕ) (hs : 2 ≤ s) (h : i.FieldsHeight s) (phase : Phase m 9) :
    pairWindow i h2 model A borrowed phase ≤
      GeneralPaperSegmentCompilerLifetime.profile model A 2 9 1 s 0 1 borrowed := by
  subst m
  exact GeneralPaperSegmentCompilerLifetime.all_phases model A _ _ s 0 1 (pair_bounds i.B A s hs h.1) borrowed phase

theorem three_bounded {m : ℕ} (i : RationalUniformGroupSpec m) (h3 : m = 3) (model : RationalCostModel)
    (A s borrowed : ℕ) (hs : 2 ≤ s) (h : i.FieldsHeight s) (phase : Phase m 9) :
    threeWindow i h3 model A borrowed phase ≤
      GeneralPaperSegmentCompilerLifetime.profile model A 3 9 5 s 20 2048 borrowed := by
  subst m
  exact GeneralPaperSegmentCompilerLifetime.all_phases model A _ _ s 20 2048
    (three_bounds i.threeInput A s hs (h.three_environment hs)) borrowed phase

theorem bounded {m : ℕ} (i : RationalUniformGroupSpec m) (size : ℕ) (hSize : size = m) (hm : m = 2 ∨ m = 3)
    (model : RationalCostModel) (A s borrowed : ℕ) (hs : 2 ≤ s) (h : i.FieldsHeight s) (phase : Phase m 9) :
    window i size hSize hm model A borrowed phase ≤ profile model A s borrowed := by
  unfold window profile
  split
  · exact (pair_bounded i _ model A s borrowed hs h phase).trans (Nat.le_add_right _ _)
  · exact (three_bounded i _ model A s borrowed hs h phase).trans (Nat.le_add_left _ _)

theorem native {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded bits model W exponent values v hv).weight j ≤ 1)
    (p : RationalTerminalPacking (GeneralPaperEqualFiniteKernel.terminal
      (GeneralPaperEqualNativeSampler.rounded bits model W exponent values v hv) small))
    (borrowed : ℕ) (phase : Phase (GeneralPaperEqualFiniteKernel.terminal
      (GeneralPaperEqualNativeSampler.rounded bits model W exponent values v hv) small).groups.length 9) :
    window (p.uniformSpec (GeneralPaperEqualFiniteKernel.no_fraction _ small)) p.groups.data.size p.groups.size
      (GeneralPaperEqualFiniteKernel.terminal _ small).groups_count model A borrowed phase ≤
      profile model A (GeneralPaperEqualNativeSampler.fieldHeight n exponent) borrowed := by
  apply bounded
  · unfold GeneralPaperEqualNativeSampler.fieldHeight
    omega
  · exact GeneralPaperEqualNativeSegmentPreparation.fields_height bits model W exponent values v hv small p

end Blotto.GeneralPaperNativeSegmentCompilerLifetime
