import Blotto.BinaryLifetimeArrayExtras
import Blotto.BinaryQuadraticSyntaxMeasured
import Blotto.BinaryThreeReferenceMeasured
import Blotto.BinaryThreeGeometryLifetime

/-! One measured five-word environment feeds measured regime and geometry
compilation/evaluation. Returned geometry words feed the regular factory.
Source constructor/control/copied-reference charges retain their native model
boundary. -/

namespace Blotto.BinaryThreeGeometryMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryThreeInputCompiler BinarySyntaxUniformWork
set_option autoImplicit false
set_option maxHeartbeats 3000000

def environment (input : Input) : (FixedArrayTable 5 SignedWord × Trace) × ℕ :=
  BinaryThreeReferenceMeasured.references 5 ![input.B,input.a,input.d,input.c,input.p]

theorem environment_data (input : Input) : (environment input).1.1 = input.environment :=
  BinaryThreeReferenceMeasured.references_data _ _

theorem environment_work (input : Input) : (environment input).2 ≤ 2324 :=
  BinaryThreeReferenceMeasured.references_work _ _

theorem environment_usage (input : Input) : usage (environment input).1.2 ≤ 1277 :=
  BinaryThreeReferenceMeasured.references_usage _ _

set_option cleanup.letToHave false in
def geometryWithExtras (env : FixedArrayTable 5 SignedWord) : ((FixedArrayTable 4 SignedWord × Trace) × ℕ) × ℕ :=
  BinaryLifetimeArrayExtras.build 4 (fun j => BinaryQuadraticSyntaxMeasured.runWithExtras env (parameters j))

def geometry (env : FixedArrayTable 5 SignedWord) : (FixedArrayTable 4 SignedWord × Trace) × ℕ :=
  (geometryWithExtras env).1

theorem geometryWithExtras_compat (env : FixedArrayTable 5 SignedWord) :
    (geometryWithExtras env).1 = geometry env := rfl

theorem geometry_record (env : FixedArrayTable 5 SignedWord) :
    geometry env =
  BinaryLifetimeArrayMeasured.build 4 (fun j => BinaryQuadraticSyntaxMeasured.run env (parameters j)) := by
  simp only [geometry,geometryWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryQuadraticSyntaxMeasured.runWithExtras_compat]

theorem geometry_data (env : FixedArrayTable 5 SignedWord) :
    (geometry env).1.1 = (BinaryThreeGeometryLifetime.geometryWithTrace env).1 := by
  simp only [geometry_record,BinaryLifetimeArrayMeasured.build_data,BinaryQuadraticSyntaxMeasured.run_erases,
    BinaryThreeGeometryLifetime.geometryWithTrace]

def geometryWork (s : ℕ) : ℕ := 4*BinaryQuadraticSyntaxMeasured.workEnvelope 16 16 s 2+1600
def geometryEnvelope (s : ℕ) : ℕ := 4*BinaryQuadraticSyntaxLifetime.bound 16 16 s 2+
  BinaryLifetimeArrayMeasured.storageReserve 4+8+BinaryQuadraticSyntaxLifetime.frames 16 s 2+10

theorem geometry_work (env : FixedArrayTable 5 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env s) : (geometry env).2 ≤ geometryWork s := by
  rw [geometry_record]
  exact BinaryLifetimeArrayMeasured.build_work_bound 4 _ _ (fun j =>
    BinaryQuadraticSyntaxMeasured.run_work env (parameters j) hC s 2 16 16 hs hH
      (BinaryOrderedThreeFactoryWork.parameter_sizes j).1 (BinaryOrderedThreeFactoryWork.parameter_sizes j).2
      (BinaryThreeGeometryLifetime.parameter_nodes j))

theorem geometry_usage (env : FixedArrayTable 5 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env s) : usage (geometry env).1.2 ≤ geometryEnvelope s := by
  rw [geometry_record]
  apply BinaryLifetimeArrayMeasured.build_bounds
  · intro j
    exact (BinaryQuadraticSyntaxMeasured.run_bounds env (parameters j) hC s 2 16 16 hs hH
      (BinaryOrderedThreeFactoryWork.parameter_sizes j).1 (BinaryOrderedThreeFactoryWork.parameter_sizes j).2
      (BinaryThreeGeometryLifetime.parameter_nodes j)).1
  · intro j
    exact (BinaryQuadraticSyntaxMeasured.run_bounds env (parameters j) hC s 2 16 16 hs hH
      (BinaryOrderedThreeFactoryWork.parameter_sizes j).1 (BinaryOrderedThreeFactoryWork.parameter_sizes j).2
      (BinaryThreeGeometryLifetime.parameter_nodes j)).2

set_option cleanup.letToHave false in
def regimeWithExtras (env : FixedArrayTable 5 SignedWord) : ((SignedWord × Trace) × ℕ) × ℕ :=
  BinaryQuadraticSyntaxMeasured.runWithExtras env BinaryThreeInputCompiler.regime

def regime (env : FixedArrayTable 5 SignedWord) : (SignedWord × Trace) × ℕ :=
  (regimeWithExtras env).1

theorem regimeWithExtras_compat (env : FixedArrayTable 5 SignedWord) :
    (regimeWithExtras env).1 = regime env := rfl

theorem regime_record (env : FixedArrayTable 5 SignedWord) :
    regime env =
  BinaryQuadraticSyntaxMeasured.run env BinaryThreeInputCompiler.regime := by
  simp only [regime,regimeWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryQuadraticSyntaxMeasured.runWithExtras_compat,geometryWithExtras_compat]

theorem regime_erases (env : FixedArrayTable 5 SignedWord) :
    (regime env).1 = BinaryThreeGeometryLifetime.regimeWithTrace env :=
  BinaryQuadraticSyntaxMeasured.run_erases _ _

def regimeWork (s : ℕ) : ℕ := BinaryQuadraticSyntaxMeasured.workEnvelope 16 8 s 2

theorem regime_work (env : FixedArrayTable 5 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env s) : (regime env).2 ≤ regimeWork s := by
  rw [regime_record]
  exact (
    BinaryQuadraticSyntaxMeasured.run_work env BinaryThreeInputCompiler.regime hC s 2 8 16 hs hH
        BinaryOrderedThreeFactoryWork.regime_sizes.1 BinaryOrderedThreeFactoryWork.regime_sizes.2
        BinaryThreeGeometryLifetime.regime_nodes
  )

theorem regime_usage (env : FixedArrayTable 5 SignedWord) (hC : ∀ j,CanonicalWord (env.read j))
    (s : ℕ) (hs : 3 ≤ s) (hH : EnvHeight env s) :
    usage (regime env).1.2 ≤ BinaryThreeGeometryLifetime.regimeEnvelope s := by
  rw [regime_erases]
  exact BinaryThreeGeometryLifetime.regimeWithTrace_usage env hC s hs hH

end Blotto.BinaryThreeGeometryMeasured
