import Blotto.BinaryCategoricalArithmeticEntryWork
import Blotto.BinaryGroupFactoryMeasured

/-! Proof-only entry charges follow the actual compiled expression, nested
regular descriptor callbacks, geometry/regime results, selected exceptional
branch and original coordinate order. No runtime callback is added. -/
namespace Blotto.BinaryThreeFactoryArithmeticEntryWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryExpressionArithmeticEntryWork (tableCost build_bound comparison_bound)
set_option autoImplicit false
set_option maxHeartbeats 5000000

def compiledCost {k : ℕ} (env : FixedArrayTable k SignedWord) (source : BinaryExpressionCompiler.Syntax k) : ℕ :=
  BinaryExpressionArithmeticEntryWork.expression env (BinaryQuadraticSyntaxMeasured.compileWithTrace source).1.1

theorem compiled_bound {k : ℕ} (env : FixedArrayTable k SignedWord) (source : BinaryExpressionCompiler.Syntax k) :
    compiledCost env source ≤ 2*listCells (BinaryQuadraticSyntaxMeasured.run env source).1.2 := by
  have h := BinaryExpressionArithmeticEntryWork.expression_bound env (BinaryQuadraticSyntaxMeasured.compileWithTrace source).1.1
  simp only [compiledCost,BinaryQuadraticSyntaxMeasured.run_record,listCells_append,listCells_under,listCells]
  omega

def vertex (env : FixedArrayTable 4 SignedWord) (i : Fin 6) : ℕ :=
  tableCost 3 (fun j => compiledCost env (BinaryThreeDescriptorCompiler.vertex i j))

theorem vertex_bound (env : FixedArrayTable 4 SignedWord) (i : Fin 6) :
    vertex env i ≤ 2*listCells (BinaryQuadraticThreeFactoryMeasured.vertexRow env i).1.2 := by
  rw [BinaryQuadraticThreeFactoryMeasured.vertexRow_record]
  exact (
    build_bound 3 _ _ (fun j => compiled_bound env (BinaryThreeDescriptorCompiler.vertex i j))
  )

def regular (env : FixedArrayTable 4 SignedWord) : ℕ :=
  tableCost 9 (fun slot => compiledCost env (BinaryThreeDescriptorCompiler.chosen slot))+
    tableCost 9 (fun slot => vertex env (RationalThreeGeometry.edges slot).1)+
    tableCost 9 (fun slot => vertex env (RationalThreeGeometry.edges slot).2)

theorem regular_bound (env : FixedArrayTable 4 SignedWord) :
    regular env ≤ 2*listCells (BinaryQuadraticThreeFactoryMeasured.descriptor env).1.2 := by
  have hw := build_bound 9 (fun slot => BinaryQuadraticSyntaxMeasured.run env (BinaryThreeDescriptorCompiler.chosen slot))
    (fun slot => compiledCost env (BinaryThreeDescriptorCompiler.chosen slot)) (fun slot => compiled_bound env _)
  have hp := build_bound 9 (fun slot => BinaryQuadraticThreeFactoryMeasured.vertexRow env (RationalThreeGeometry.edges slot).1)
    (fun slot => vertex env (RationalThreeGeometry.edges slot).1) (fun slot => vertex_bound env _)
  have hq := build_bound 9 (fun slot => BinaryQuadraticThreeFactoryMeasured.vertexRow env (RationalThreeGeometry.edges slot).2)
    (fun slot => vertex env (RationalThreeGeometry.edges slot).2) (fun slot => vertex_bound env _)
  simp only [regular,BinaryQuadraticThreeFactoryMeasured.descriptor_record,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def geometry (env : FixedArrayTable 5 SignedWord) : ℕ :=
  tableCost 4 (fun j => compiledCost env (BinaryThreeInputCompiler.parameters j))

theorem geometry_bound (env : FixedArrayTable 5 SignedWord) :
    geometry env ≤ 2*listCells (BinaryThreeGeometryMeasured.geometry env).1.2 := by
  rw [BinaryThreeGeometryMeasured.geometry_record]
  exact (
    build_bound 4 _ _ (fun j => compiled_bound env (BinaryThreeInputCompiler.parameters j))
  )

def ordered (input : BinaryThreeInputCompiler.Input) : ℕ :=
  let env := BinaryThreeGeometryMeasured.environment input
  let regime := BinaryThreeGeometryMeasured.regime env.1.1
  let compared := BinaryQuadraticExpressionMeasured.compare regime.1.1 BinaryRationalOpcode.zero
  compiledCost env.1.1 BinaryThreeInputCompiler.regime+
    BinaryArithmeticEntryWork.comparison regime.1.1 BinaryRationalOpcode.zero+
    if !compared.1.1 then
      geometry env.1.1+regular (BinaryThreeGeometryMeasured.geometry env.1.1).1.1
    else 0

theorem ordered_bound (input : BinaryThreeInputCompiler.Input) :
    ordered input ≤ 2*listCells (BinaryThreeFactoryMeasured.ordered input).1.2 := by
  let env := (BinaryThreeGeometryMeasured.environment input).1.1
  have hr := compiled_bound env BinaryThreeInputCompiler.regime
  have hc := comparison_bound (BinaryThreeGeometryMeasured.regime env).1.1 BinaryRationalOpcode.zero
  have hg := geometry_bound env
  have hf := regular_bound (BinaryThreeGeometryMeasured.geometry env).1.1
  dsimp only [env] at hr hc hg hf
  simp only [ordered,BinaryThreeFactoryMeasured.ordered_record]
  split <;> simp only [BinaryThreeGeometryMeasured.regime_record,wrap,combine,listCells_append,listCells_under,listCells] at hr hc ⊢ <;> omega

def descriptor (input : BinaryThreeInputCompiler.Input) : ℕ :=
  let order := BinaryQuadraticExpressionMeasured.compare input.a input.d
  BinaryArithmeticEntryWork.comparison input.a input.d+
    ordered (if order.1.1 then input else ⟨input.B,input.d,input.a,input.c,input.p⟩)

theorem descriptor_bound (input : BinaryThreeInputCompiler.Input) :
    descriptor input ≤ 2*listCells (BinaryThreeFactoryMeasured.descriptor input).1.2 := by
  have ho := comparison_bound input.a input.d
  have hc := ordered_bound (if (BinaryQuadraticExpressionMeasured.compare input.a input.d).1.1 then input
    else ⟨input.B,input.d,input.a,input.c,input.p⟩)
  simp only [descriptor,BinaryThreeFactoryMeasured.descriptor_record,BinaryThreeFactoryMeasured.restore]
  split <;> simp_all only [Bool.false_eq_true,ite_true,ite_false,wrap,combine,listCells_append,listCells_under,listCells] <;> omega

def uniformFactory {m : ℕ} (input : BinaryGroupInputs.UniformInput m) (hm : m=2 ∨ m=3) : ℕ := by
  by_cases hTwo : m=2
  · exact 0
  · have hThree : m=3 := hm.resolve_left hTwo
    subst m
    exact descriptor (BinaryGroupInputs.uniformThree input)

theorem uniformFactory_bound {m : ℕ} (input : BinaryGroupInputs.UniformInput m) (hm : m=2 ∨ m=3) :
    uniformFactory input hm ≤ 2*listCells (BinaryGroupFactoryMeasured.uniformFactory input hm).1.2 := by
  rcases hm with rfl | rfl
  · simp only [uniformFactory,BinaryGroupFactoryMeasured.uniformFactory_record,dif_pos rfl,dite_true,dite_false]
    omega
  · have h := descriptor_bound (BinaryGroupInputs.uniformThree input)
    simp only [uniformFactory,BinaryGroupFactoryMeasured.uniformFactory_record,show ¬(3:ℕ)=2 by decide,dif_neg,dite_true,dite_false,
      wrap,combine,listCells_append,listCells_under,listCells]
    omega

theorem uniformPrepared_bound {m : ℕ} (input : BinaryGroupInputs.UniformInput m) (hC : input.Canonical)
    (hAd : BinaryGroupSamplers.UniformAdmissible input) (hm : m=2 ∨ m=3) :
    uniformFactory input hm ≤ 2*listCells (BinaryGroupFactoryMeasured.uniformPrepared input hC hAd hm).1.2 := by
  have h := uniformFactory_bound input hm
  simp only [BinaryGroupFactoryMeasured.uniformPrepared_record,wrap,combine,listCells_append,listCells_under,listCells]
  omega

theorem mixedTwoPrepared_bound (input : BinaryGroupInputs.MixedInput 2) (hC : input.Canonical)
    (hAd : BinaryGroupSamplers.MixedAdmissible input) :
    descriptor (BinaryGroupInputs.mixedThree input) ≤
      2*listCells (BinaryGroupFactoryMeasured.mixedTwoPrepared input hC hAd).1.2 := by
  have h := descriptor_bound (BinaryGroupInputs.mixedThree input)
  simp only [BinaryGroupFactoryMeasured.mixedTwoPrepared_record,wrap,combine,listCells_append,listCells_under,listCells]
  omega

end Blotto.BinaryThreeFactoryArithmeticEntryWork
