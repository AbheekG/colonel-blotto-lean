import Blotto.BinaryExpressionNormalizationExtras
import Blotto.BinaryQuadraticThreeFactoryMeasured
import Blotto.BinaryThreeGeometryMeasured
import Blotto.BinaryOverlapGluingMeasured
import Blotto.BinaryFourParametersMeasured
import Blotto.BinaryNestedParameterMeasured
import Blotto.BinaryNestedResidualDescriptorMeasured

/-! Actual callback arrays retain expression normalization extras without replay.
The returned field fits155 times the old source work, and complete source plus
extra fits156 times each ORIGINAL component price under all original premises.
Old trace-usage bounds retain their stated source-event scope. Root forwarding
and native counter/record/physical costs remain separate obligations. -/
namespace Blotto.BinaryFactoryExpressionExtras
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinarySyntaxUniformWork
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeFactory
open BinaryQuadraticThreeFactoryMeasured

theorem vertexRow_extra (env : FixedArrayTable 4 SignedWord) (i : Fin 6) :
    (vertexRowWithExtras env i).2 ≤ 155*(vertexRowWithExtras env i).1.2 :=
  BinaryLifetimeArrayExtras.build_bound 3 _ 155 (fun j => BinaryExpressionNormalizationExtras.syntax_bound env (BinaryThreeDescriptorCompiler.vertex i j))

theorem descriptor_extra (env : FixedArrayTable 4 SignedWord) :
    (descriptorWithExtras env).2 ≤ 155*(descriptorWithExtras env).1.2 := by
  have hw := BinaryLifetimeArrayExtras.build_bound 9 (fun slot => BinaryQuadraticSyntaxMeasured.runWithExtras env (BinaryThreeDescriptorCompiler.chosen slot)) 155 (fun slot => BinaryExpressionNormalizationExtras.syntax_bound env _)
  have hp := BinaryLifetimeArrayExtras.build_bound 9 (fun slot => vertexRowWithExtras env (RationalThreeGeometry.edges slot).1) 155 (fun slot => vertexRow_extra env _)
  have hq := BinaryLifetimeArrayExtras.build_bound 9 (fun slot => vertexRowWithExtras env (RationalThreeGeometry.edges slot).2) 155 (fun slot => vertexRow_extra env _)
  simp only [descriptorWithExtras]
  omega

theorem vertexRow_price (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env s) (i : Fin 6) :
    (vertexRowWithExtras env i).1.2+(vertexRowWithExtras env i).2 ≤ 156*(3*expressionWork s+1024) := by
  have he := vertexRow_extra env i
  have ho := vertexRow_work env hC s hs hH i
  simp only [vertexRowWithExtras_compat] at he ⊢
  omega

theorem descriptor_price (env : FixedArrayTable 4 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env s) : (descriptorWithExtras env).1.2+(descriptorWithExtras env).2 ≤ 156*(workEnvelope s) := by
  have he := descriptor_extra env
  have ho := descriptor_work env hC s hs hH
  simp only [descriptorWithExtras_compat] at he ⊢
  omega

end ThreeFactory

namespace ThreeGeometry
open BinaryThreeGeometryMeasured
open BinaryThreeInputCompiler

theorem geometry_extra (env : FixedArrayTable 5 SignedWord) :
    (geometryWithExtras env).2 ≤ 155*(geometryWithExtras env).1.2 :=
  BinaryLifetimeArrayExtras.build_bound 4 _ 155 (fun j => BinaryExpressionNormalizationExtras.syntax_bound env (parameters j))

theorem regime_extra (env : FixedArrayTable 5 SignedWord) :
    (regimeWithExtras env).2 ≤ 155*(regimeWithExtras env).1.2 :=
  BinaryExpressionNormalizationExtras.syntax_bound env BinaryThreeInputCompiler.regime

theorem geometry_price (env : FixedArrayTable 5 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env s) : (geometryWithExtras env).1.2+(geometryWithExtras env).2 ≤ 156*(geometryWork s) := by
  have he := geometry_extra env
  have ho := geometry_work env hC s hs hH
  simp only [geometryWithExtras_compat] at he ⊢
  omega

theorem regime_price (env : FixedArrayTable 5 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env s) : (regimeWithExtras env).1.2+(regimeWithExtras env).2 ≤ 156*(regimeWork s) := by
  have he := regime_extra env
  have ho := regime_work env hC s hs hH
  simp only [regimeWithExtras_compat] at he ⊢
  omega

end ThreeGeometry

namespace Gluing
open BinaryOverlapGluingMeasured
open BinaryStoredOverlapEnvironment

theorem fromEnvironment_extra (env : (FixedArrayTable 16 SignedWord × Trace) × ℕ) :
    (fromEnvironmentWithExtras env).2 ≤ 155*(fromEnvironmentWithExtras env).1.2 := by
  have hw := BinaryExpressionNormalizationExtras.syntax_bound env.1.1 BinaryOverlapCompilerBridge.weight
  have hp := BinaryLifetimeArrayExtras.build_bound 4 (fun j => BinaryQuadraticSyntaxMeasured.runWithExtras env.1.1 (BinaryOverlapCompilerBridge.safeP j)) 155 (fun j => BinaryExpressionNormalizationExtras.syntax_bound env.1.1 _)
  have hq := BinaryLifetimeArrayExtras.build_bound 4 (fun j => BinaryQuadraticSyntaxMeasured.runWithExtras env.1.1 (BinaryOverlapCompilerBridge.safeQ j)) 155 (fun j => BinaryExpressionNormalizationExtras.syntax_bound env.1.1 _)
  simp only [fromEnvironmentWithExtras,collect]
  omega

theorem slot_extra {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h)
    (interval budget : SignedWord) (i : Fin k) (j : Fin h) :
    (slotWithExtras first second interval budget i j).2 ≤ 155*(slotWithExtras first second interval budget i j).1.2 :=
  fromEnvironment_extra _

theorem descriptor_extra {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h) (interval budget : SignedWord) :
    (descriptorWithExtras first second interval budget).2 ≤ 155*(descriptorWithExtras first second interval budget).1.2 := by
  have hs := BinaryLifetimeArrayExtras.build_bound (k*h) (fun index => slotWithExtras first second interval budget (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2) 155 (fun index => slot_extra first second interval budget _ _)
  simp only [descriptorWithExtras]
  omega

theorem fromEnvironment_price (env : (FixedArrayTable 16 SignedWord × Trace) × ℕ)
    (hEnvW : env.2 ≤ 18560) (hEnvU : usage env.1.2 ≤ 9483)
    (hC : ∀ r,CanonicalWord (env.1.1.read r)) (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env.1.1 s) :
    (fromEnvironmentWithExtras env).1.2+(fromEnvironmentWithExtras env).2 ≤ 156*(slotPrice s) ∧ usage (fromEnvironmentWithExtras env).1.1.2 ≤ slotEnvelope s := by
  have he := fromEnvironment_extra env
  have ho := fromEnvironment_bounds env hEnvW hEnvU hC s hs hH
  simp only [fromEnvironmentWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem slot_price {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h) (interval budget : SignedWord) (i : Fin k) (j : Fin h)
    (hFirst : first.Canonical) (hSecond : second.Canonical) (hInterval : CanonicalWord interval) (hBudget : CanonicalWord budget)
    (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight (BinaryStoredOverlapEnvironment.environment first second interval budget i j) s) :
    (slotWithExtras first second interval budget i j).1.2+(slotWithExtras first second interval budget i j).2 ≤ 156*(slotPrice s) ∧ usage (slotWithExtras first second interval budget i j).1.1.2 ≤ slotEnvelope s := by
  have he := slot_extra first second interval budget i j
  have ho := slot_bounds first second interval budget i j hFirst hSecond hInterval hBudget s hs hH
  simp only [slotWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem descriptor_price {k h : ℕ} (first : Segment 3 k) (second : Segment 3 h) (interval budget : SignedWord)
    (hFirst : first.Canonical) (hSecond : second.Canonical) (hInterval : CanonicalWord interval) (hBudget : CanonicalWord budget)
    (s : ℕ) (hs : 3 ≤ s) (hH : ∀ i j,EnvHeight (BinaryStoredOverlapEnvironment.environment first second interval budget i j) s) :
    (descriptorWithExtras first second interval budget).1.2+(descriptorWithExtras first second interval budget).2 ≤ 156*(workEnvelope (k*h) s) ∧
      usage (descriptorWithExtras first second interval budget).1.1.2 ≤ envelope (k*h) s := by
  have he := descriptor_extra first second interval budget
  have ho := descriptor_bounds first second interval budget hFirst hSecond hInterval hBudget s hs hH
  simp only [descriptorWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end Gluing

namespace FourParameters
open BinaryFourParametersMeasured
open BinaryFourParameters

theorem prepare_extra (input : Input) :
    (prepareWithExtras input).2 ≤ 155*(prepareWithExtras input).1.2 := by
  have h := BinaryLifetimeArrayExtras.build_bound 8 (fun j => BinaryQuadraticSyntaxMeasured.runWithExtras (environment input).1.1 (programs j)) 155 (fun j => BinaryExpressionNormalizationExtras.syntax_bound (environment input).1.1 _)
  simp only [prepareWithExtras]
  omega

theorem prepare_price (input : Input) (source : RationalFourInput) (hC : input.Canonical) (hR : input.Refines source)
    (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s) :
    (prepareWithExtras input).1.2+(prepareWithExtras input).2 ≤ 156*(workEnvelope s) ∧ usage (prepareWithExtras input).1.1.2 ≤ envelope s := by
  have he := prepare_extra input
  have ho := prepare_bounds input source hC hR s hs hH
  simp only [prepareWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end FourParameters

namespace NestedParameters
open BinaryNestedParameterMeasured

theorem runPrograms_extra (n : ℕ) (programs : Fin n → BinaryExpressionCompiler.Syntax 7)
    (input : Input) (x : SignedWord) (cells frames : ℕ) :
    (runProgramsWithExtras n programs input x cells frames).2 ≤ 155*(runProgramsWithExtras n programs input x cells frames).1.2 := by
  have h := BinaryLifetimeArrayExtras.build_bound n (fun j => BinaryQuadraticSyntaxMeasured.runWithExtras (environment input x).1.1 (programs j)) 155 (fun j => BinaryExpressionNormalizationExtras.syntax_bound (environment input x).1.1 _)
  simp only [runProgramsWithExtras]
  omega

theorem prepareAt_extra (input : Input) (x : SignedWord) :
    (prepareAtWithExtras input x).2 ≤ 155*(prepareAtWithExtras input x).1.2 := runPrograms_extra _ _ _ _ _ _

theorem prepare_extra (input : Input) :
    (prepareWithExtras input).2 ≤ 155*(prepareWithExtras input).1.2 := prepareAt_extra _ _

theorem geometry_extra (input : Input) (x : SignedWord) :
    (geometryWithExtras input x).2 ≤ 155*(geometryWithExtras input x).1.2 := runPrograms_extra _ _ _ _ _ _

theorem runPrograms_price (n : ℕ) (programs : Fin n → BinaryExpressionCompiler.Syntax 7)
    (input : Input) (x : SignedWord) (cells frames : ℕ) (hC : input.Canonical) (hX : CanonicalWord x)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (hXH : RationalHeight (value x) s)
    (hDepth : ∀ j,(programs j).rational.depth ≤ 16)
    (hOps : ∀ j,(programs j).rational.operationBound ≤ 256) (hNodes : ∀ j,(programs j).nodes ≤ 256) :
    (runProgramsWithExtras n programs input x cells frames).1.2+(runProgramsWithExtras n programs input x cells frames).2 ≤ 156*(workEnvelope n s) ∧
      usage (runProgramsWithExtras n programs input x cells frames).1.1.2 ≤ envelope n s cells frames := by
  have he := runPrograms_extra n programs input x cells frames
  have ho := runPrograms_bounds n programs input x cells frames hC hX s hs hH hXH hDepth hOps hNodes
  simp only [runProgramsWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem prepareAt_price (input : Input) (x : SignedWord) (hC : input.Canonical) (hX : CanonicalWord x)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (hXH : RationalHeight (value x) s) :
    (prepareAtWithExtras input x).1.2+(prepareAtWithExtras input x).2 ≤ 156*(workEnvelope 9 s) ∧ usage (prepareAtWithExtras input x).1.1.2 ≤ envelope 9 s 128 10 := by
  have he := prepareAt_extra input x
  have ho := prepareAt_bounds input x hC hX s hs hH hXH
  simp only [prepareAtWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem prepare_price (input : Input) (hC : input.Canonical)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) :
    (prepareWithExtras input).1.2+(prepareWithExtras input).2 ≤ 156*(workEnvelope 9 s) ∧ usage (prepareWithExtras input).1.1.2 ≤ envelope 9 s 128 10 := by
  have he := prepare_extra input
  have ho := prepare_bounds input hC s hs hH
  simp only [prepareWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem geometry_price (input : Input) (x : SignedWord) (hC : input.Canonical) (hX : CanonicalWord x)
    (s : ℕ) (hs : 3 ≤ s) (hH : BinaryNestedParameterWork.InputHeight input s) (hXH : RationalHeight (value x) s) :
    (geometryWithExtras input x).1.2+(geometryWithExtras input x).2 ≤ 156*(workEnvelope 4 s) ∧ usage (geometryWithExtras input x).1.1.2 ≤ envelope 4 s 96 8 := by
  have he := geometry_extra input x
  have ho := geometry_bounds input x hC hX s hs hH hXH
  simp only [geometryWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end NestedParameters

namespace Residual
open BinaryNestedResidualDescriptorMeasured
open BinaryNestedResidualCompiler

theorem weights_extra (env : Env) :
    (weightsWithExtras env).2 ≤ 155*(weightsWithExtras env).1.2 :=
  BinaryLifetimeArrayExtras.build_bound 3 _ 155 (fun j => BinaryExpressionNormalizationExtras.syntax_bound env (BinaryNestedResidualCompiler.weights j))

theorem vertexRow_extra (env : Env) (vertex : Fin 3) :
    (vertexRowWithExtras env vertex).2 ≤ 155*(vertexRowWithExtras env vertex).1.2 :=
  BinaryLifetimeArrayExtras.build_bound 3 _ 155 (fun j => BinaryExpressionNormalizationExtras.syntax_bound env (vertices vertex j))

theorem rows_extra (env : Env) (edge : Fin 3 → Fin 3) :
    (rowsWithExtras env edge).2 ≤ 155*(rowsWithExtras env edge).1.2 :=
  BinaryLifetimeArrayExtras.build_bound 3 _ 155 (fun j => vertexRow_extra env (edge j))

theorem descriptor_extra (env : Env) :
    (descriptorWithExtras env).2 ≤ 155*(descriptorWithExtras env).1.2 := by
  have hw := weights_extra env
  have hp := rows_extra env (fun slot => (RationalNestedResidual.edges slot).1)
  have hq := rows_extra env (fun slot => (RationalNestedResidual.edges slot).2)
  simp only [descriptorWithExtras]
  omega

theorem weights_price (env : Env) (hC : ∀ j,CanonicalWord (env.read j)) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinarySyntaxUniformWork.EnvHeight env s) :
    (weightsWithExtras env).1.2+(weightsWithExtras env).2 ≤ 156*(arrayPrice (expressionWork s)) ∧ usage (weightsWithExtras env).1.1.2 ≤ arrayEnvelope (expressionEnvelope s) := by
  have he := weights_extra env
  have ho := weights_bounds env hC s hs hH
  simp only [weightsWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem vertexRow_price (env : Env) (hC : ∀ j,CanonicalWord (env.read j)) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinarySyntaxUniformWork.EnvHeight env s) (vertex : Fin 3) :
    (vertexRowWithExtras env vertex).1.2+(vertexRowWithExtras env vertex).2 ≤ 156*(arrayPrice (expressionWork s)) ∧ usage (vertexRowWithExtras env vertex).1.1.2 ≤ arrayEnvelope (expressionEnvelope s) := by
  have he := vertexRow_extra env vertex
  have ho := vertexRow_bounds env hC s hs hH vertex
  simp only [vertexRowWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem rows_price (env : Env) (edge : Fin 3 → Fin 3) (hC : ∀ j,CanonicalWord (env.read j)) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinarySyntaxUniformWork.EnvHeight env s) :
    (rowsWithExtras env edge).1.2+(rowsWithExtras env edge).2 ≤ 156*(arrayPrice (arrayPrice (expressionWork s))) ∧
      usage (rowsWithExtras env edge).1.1.2 ≤ arrayEnvelope (arrayEnvelope (expressionEnvelope s)) := by
  have he := rows_extra env edge
  have ho := rows_bounds env edge hC s hs hH
  simp only [rowsWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

theorem descriptor_price (env : Env) (hC : ∀ j,CanonicalWord (env.read j)) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinarySyntaxUniformWork.EnvHeight env s) :
    (descriptorWithExtras env).1.2+(descriptorWithExtras env).2 ≤ 156*(workEnvelope s) ∧ usage (descriptorWithExtras env).1.1.2 ≤ envelope s := by
  have he := descriptor_extra env
  have ho := descriptor_bounds env hC s hs hH
  simp only [descriptorWithExtras_compat] at he ⊢
  exact ⟨by omega,ho.2⟩

end Residual

end Blotto.BinaryFactoryExpressionExtras
