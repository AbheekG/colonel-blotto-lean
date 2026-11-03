import Blotto.GeneralPaperFixedEnvironmentLifetime

/-! Environment construction, all nested compiler phases and factory return
are covered in one envelope. Factory cost/control fields remain live while
the compiler runs. The calling owner retains fixed code and cached inputs. -/
namespace Blotto.GeneralPaperFixedSegmentFactoryLifetime
open GeneralPaperEncodedScalarStorage (natBits fields)
open GeneralPaperSegmentExpressionCompiler (Programs)
open GeneralPaperSegmentCompilerStorage (Bounds)
open GeneralPaperFixedEnvironmentLifetime (copy)
set_option autoImplicit false
set_option maxHeartbeats 1600000

inductive Phase (n r k : ℕ) where
  | environment (phase : GeneralPaperFixedEnvironmentLifetime.Phase k)
  | compiler (phase : GeneralPaperSegmentCompilerLifetime.Phase n r)
  | returned

def actual {n r k : ℕ} {l : RationalSegmentLottery n r} (model : RationalCostModel) (A : ℕ)
    (values : Fin k → ℚ) (p : Programs l (copy A values).1) : PreparedSegmentDescriptor l × ℕ :=
  let env := copy A values
  let compiled := GeneralPaperSegmentExpressionCompiler.run model A env.1 p
  (compiled.1, env.2 + compiled.2 + 64 * A + 64)

def cap (model : RationalCostModel) (A n r k s d M : ℕ) : ℕ :=
  GeneralPaperFixedEnvironmentLifetime.time A k s + GeneralPaperSegmentCompilerStorage.compilerTime model A n r k s d M + 64 * A + 64

def controls {k : ℕ} (A : ℕ) (values : Fin k → ℚ) : ℕ := fields A [(copy A values).2, 64 * A, 64] + 128 * A

def controlProfile (model : RationalCostModel) (A n r k s d M : ℕ) : ℕ :=
  3 * (natBits (cap model A n r k s d M) + A) + 160 * A

theorem controls_bound {n r k : ℕ} (model : RationalCostModel) (A s d M : ℕ)
    (values : Fin k → ℚ) (hValues : ∀ j, RationalHeight (values j) s) :
    controls A values ≤ controlProfile model A n r k s d M := by
  have hWork := GeneralPaperFixedEnvironmentLifetime.work A s values hValues
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (cap model A n r k s d M)
    [(copy A values).2, 64 * A, 64] (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> unfold cap <;> omega)
  change fields A _ ≤ 3 * (natBits (cap model A n r k s d M) + A) + 32 * A at hFields
  unfold controls controlProfile
  omega

def window {n r k : ℕ} {l : RationalSegmentLottery n r} (model : RationalCostModel) (A : ℕ)
    (values : Fin k → ℚ) (p : Programs l (copy A values).1) (borrowed : ℕ) : Phase n r k → ℕ
  | .environment phase => GeneralPaperFixedEnvironmentLifetime.window A values borrowed phase
  | .compiler phase => GeneralPaperSegmentCompilerLifetime.window model A (copy A values).1 p (borrowed + controls A values) phase
  | .returned => GeneralPaperSegmentCompilerStorage.assemblyWindow model A (copy A values).1 p borrowed +
      fields A [(copy A values).2, (actual model A values p).2, 64 * A] + 128 * A

def profile (model : RationalCostModel) (A n r k s d M borrowed : ℕ) : ℕ :=
  GeneralPaperFixedEnvironmentLifetime.profile A k s borrowed +
    GeneralPaperSegmentCompilerLifetime.profile model A n r k s d M
      (borrowed + controlProfile model A n r k s d M) +
    GeneralPaperSegmentCompilerStorage.assemblyProfile model A n r k s d M borrowed +
    controlProfile model A n r k s d M

theorem borrowed_mono (model : RationalCostModel) (A n r k s d M B C : ℕ) (h : B ≤ C) :
    GeneralPaperSegmentCompilerLifetime.profile model A n r k s d M B ≤
      GeneralPaperSegmentCompilerLifetime.profile model A n r k s d M C := by
  unfold GeneralPaperSegmentCompilerLifetime.profile GeneralPaperExpressionRowLifetime.profile
    GeneralPaperExpressionArrayReturns.rowProfile GeneralPaperExpressionArrayReturns.matrixProfile
    GeneralPaperExpressionMatrixLifetime.activeProfile GeneralPaperSegmentCompilerStorage.assemblyProfile
  omega

theorem all_phases {n r k : ℕ} {l : RationalSegmentLottery n r} (model : RationalCostModel) (A : ℕ)
    (values : Fin k → ℚ) (p : Programs l (copy A values).1) (s d M : ℕ)
    (hValues : ∀ j, RationalHeight (values j) s) (h : Bounds p s d M)
    (borrowed : ℕ) (phase : Phase n r k) : window model A values p borrowed phase ≤ profile model A n r k s d M borrowed := by
  have hControls := controls_bound (n := n) (r := r) model A s d M values hValues
  cases phase with
  | environment phase =>
    have hEnv := GeneralPaperFixedEnvironmentLifetime.all_phases A s values hValues borrowed phase
    simp only [window, profile]
    omega
  | compiler phase =>
    have hCompiler := GeneralPaperSegmentCompilerLifetime.all_phases model A (copy A values).1 p s d M h
      (borrowed + controls A values) phase
    have hMono := borrowed_mono model A n r k s d M _ _ (Nat.add_le_add_left hControls borrowed)
    simp only [window, profile]
    exact (hCompiler.trans hMono).trans (by omega)
  | returned =>
    have hAssembly := GeneralPaperSegmentCompilerStorage.assembly model A (copy A values).1 p s d M h borrowed
    have hEnv := GeneralPaperFixedEnvironmentLifetime.work A s values hValues
    have hCompiled := GeneralPaperSegmentCompilerStorage.compiler_work model A (copy A values).1 p s d M h
    have hActual : (actual model A values p).2 ≤ cap model A n r k s d M := by
      change (copy A values).2 + (GeneralPaperSegmentExpressionCompiler.run model A (copy A values).1 p).2 + 64 * A + 64 ≤ _
      unfold cap
      omega
    have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (cap model A n r k s d M)
      [(copy A values).2, (actual model A values p).2, 64 * A] (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;> unfold cap at * <;> omega)
    change fields A _ ≤ 3 * (natBits (cap model A n r k s d M) + A) + 32 * A at hFields
    simp only [window, profile]
    unfold controlProfile
    omega

theorem data {n r k : ℕ} {l : RationalSegmentLottery n r} (model : RationalCostModel) (A : ℕ)
    (values : Fin k → ℚ) (p : Programs l (copy A values).1) :
    (actual model A values p).1 = PreparedSegmentDescriptor.prepare l := GeneralPaperSegmentExpressionCompiler.unique _ _

end Blotto.GeneralPaperFixedSegmentFactoryLifetime
