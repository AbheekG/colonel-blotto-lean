import Blotto.BinaryNestedControlArithmeticEntryWork
import Blotto.BinaryNestedProfileMeasured

/-! Actual nested locations, chosen descriptors, family lotteries, residual
programs and binary mixtures supply the complete nested-profile entry sum.
Reference padding/restoration adds no raw/comparison entry scans. -/
namespace Blotto.BinaryNestedProfileArithmeticEntryWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryExpressionArithmeticEntryWork (tableCost build_bound quadratic_bound comparison_bound)
open BinaryThreeFactoryArithmeticEntryWork (compiledCost compiled_bound)
open BinaryNestedControlArithmeticEntryWork (Input programs programs_bound control control_bound)
set_option autoImplicit false
set_option maxHeartbeats 5000000
abbrev Small := BinaryStoredOverlapEnvironment.Segment 3 9

def shiftRow (row : FixedArrayTable 3 SignedWord) (x : SignedWord) : ℕ := BinaryArithmeticEntryWork.raw .add (row.read 2) x

theorem shiftRow_bound (row : FixedArrayTable 3 SignedWord) (x : SignedWord) :
    shiftRow row x ≤ 2*listCells (BinaryNestedFirstAssemblyMeasured.rowShift row x).1.2 := by
  have h := quadratic_bound .add (row.read 2) x
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,shiftRow,BinaryNestedFirstAssemblyMeasured.rowShift_record,BinaryNestedFirstAssemblyMeasured.rowFrom,
    wrap,combine,listCells_append,listCells_under,listCells]
  omega

def shiftRows (rows : FixedArrayTable 9 (FixedArrayTable 3 SignedWord)) (x : SignedWord) : ℕ :=
  tableCost 9 (fun slot => shiftRow (rows.read slot) x)

theorem shiftRows_bound (rows : FixedArrayTable 9 (FixedArrayTable 3 SignedWord)) (x : SignedWord) :
    shiftRows rows x ≤ 2*listCells (BinaryNestedFirstAssemblyMeasured.rowsShift rows x).1.2 := by
  rw [BinaryNestedFirstAssemblyMeasured.rowsShift_record]
  exact (
    build_bound 9 _ _ (fun _slot => shiftRow_bound _ _)
  )

def shift (table : Small) (x : SignedWord) : ℕ := shiftRows table.P x+shiftRows table.Q x

theorem shift_bound (table : Small) (x : SignedWord) : shift table x ≤ 2*listCells (BinaryNestedFirstAssemblyMeasured.shift table x).1.2 := by
  have hp := shiftRows_bound table.P x
  have hq := shiftRows_bound table.Q x
  simp only [shift,BinaryNestedFirstAssemblyMeasured.shift_record,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def location (input : Input) (K : ℕ) (bits : BinaryScalarTape K) : ℕ :=
  programs 9 BinaryNestedParameters.programs input (BinaryNestedFirstLocationMeasured.midpoint K bits).1.1

theorem location_bound (input : Input) (K : ℕ) (bits : BinaryScalarTape K) :
    location input K bits ≤ 2*listCells (BinaryNestedFirstLocationMeasured.location input K bits).1.2 := by
  have h := programs_bound 9 BinaryNestedParameters.programs input (BinaryNestedFirstLocationMeasured.midpoint K bits).1.1 128 10
  simp only [location,BinaryNestedFirstLocationMeasured.location_record,BinaryNestedFirstLocationMeasured.collect,
    BinaryNestedParameterMeasured.prepareAt_record,wrapList,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def positive (input : Input) (x : SignedWord) : ℕ :=
  let geometry := BinaryNestedParameterMeasured.geometry input x
  let table := BinaryQuadraticThreeFactoryMeasured.descriptor geometry.1.1
  programs 4 BinaryNestedParameters.firstParameters input x+
    BinaryThreeFactoryArithmeticEntryWork.regular geometry.1.1+shift table.1.1 x

theorem positive_bound (input : Input) (x : SignedWord) :
    positive input x ≤ 2*listCells (BinaryNestedFirstDescriptorMeasured.positive input x).1.2 := by
  have hg := programs_bound 4 BinaryNestedParameters.firstParameters input x 96 8
  have ht := BinaryThreeFactoryArithmeticEntryWork.regular_bound (BinaryNestedParameterMeasured.geometry input x).1.1
  have hs := shift_bound (BinaryQuadraticThreeFactoryMeasured.descriptor (BinaryNestedParameterMeasured.geometry input x).1.1).1.1 x
  simp only [positive,BinaryNestedFirstDescriptorMeasured.positive_record,BinaryNestedFirstDescriptorMeasured.positiveFrom_record,
    BinaryNestedFirstDescriptorMeasured.joinPositive,BinaryNestedParameterMeasured.geometry_record,
    wrap,combine,listCells_append,listCells_under,listCells] at hg ht hs ⊢
  omega

def descriptor (input : Input) (x : SignedWord) : ℕ :=
  let parameters := BinaryNestedParameterMeasured.prepareAt input x
  let guard := BinaryQuadraticExpressionMeasured.compare (parameters.1.1.read 4) BinaryRationalOpcode.zero
  programs 9 BinaryNestedParameters.programs input x+
    BinaryArithmeticEntryWork.comparison (parameters.1.1.read 4) BinaryRationalOpcode.zero+
      if !guard.1.1 then positive input x else 0

theorem descriptor_bound (input : Input) (x : SignedWord) :
    descriptor input x ≤ 2*listCells (BinaryNestedFirstDescriptorMeasured.descriptor input x).1.2 := by
  have hp := programs_bound 9 BinaryNestedParameters.programs input x 128 10
  have hg := comparison_bound ((BinaryNestedParameterMeasured.prepareAt input x).1.1.read 4) BinaryRationalOpcode.zero
  have ht := positive_bound input x
  change programs 9 BinaryNestedParameters.programs input x ≤ 2*listCells (BinaryNestedParameterMeasured.prepareAt input x).1.2 at hp
  simp only [descriptor,BinaryNestedFirstDescriptorMeasured.descriptor_record,BinaryNestedFirstDescriptorMeasured.fromParameters_record,
    BinaryNestedFirstDescriptorMeasured.finish]
  split_ifs <;> simp only [wrap,combine,listCells_append,listCells_under,listCells] <;> omega

def first (input : Input) (K : ℕ) (bits : BinaryScalarTape K) : ℕ :=
  location input K bits+descriptor input (BinaryNestedFirstLocationMeasured.location input K bits).1.1

theorem first_bound (input : Input) (K : ℕ) (bits : BinaryScalarTape K) :
    first input K bits ≤ 2*listCells (BinaryNestedFirstProfileMeasured.profile input K bits).1.2 := by
  have hl := location_bound input K bits
  have hd := descriptor_bound input (BinaryNestedFirstLocationMeasured.location input K bits).1.1
  simp only [first,BinaryNestedFirstProfileMeasured.profile_record,BinaryNestedFirstProfileMeasured.collect,
    wrap,combine,listCells_append,listCells_under,listCells]
  omega

def family (input : Input) (length : SignedWord) (K : ℕ) (bits : BinaryScalarTape K) : ℕ :=
  let prepared := BinaryNestedFamilyMeasured.prepare input length
  let located := BinaryNestedFirstLocationMeasured.location prepared.1.1 K bits
  programs 9 BinaryNestedParameters.programs input length+location prepared.1.1 K bits+descriptor prepared.1.1 located.1.1

theorem family_bound (input : Input) (length : SignedWord) (K : ℕ) (bits : BinaryScalarTape K) :
    family input length K bits ≤ 2*listCells (BinaryNestedFamilyMeasured.lottery input length K bits).1.2 := by
  have hp := programs_bound 9 BinaryNestedParameters.programs input length 128 10
  have hl := location_bound (BinaryNestedFamilyMeasured.prepare input length).1.1 K bits
  have hd := descriptor_bound (BinaryNestedFamilyMeasured.prepare input length).1.1
    (BinaryNestedFirstLocationMeasured.location (BinaryNestedFamilyMeasured.prepare input length).1.1 K bits).1.1
  change programs 9 BinaryNestedParameters.programs input length ≤ 2*listCells (BinaryNestedParameterMeasured.prepareAt input length).1.2 at hp
  simp only [family,BinaryNestedFamilyMeasured.lottery_record,BinaryNestedFamilyMeasured.fromFamily_record,BinaryNestedFamilyMeasured.collect,
    BinaryNestedFamilyMeasured.prepare_record,BinaryNestedFamilyMeasured.inputFrom,
    wrap,combine,listCells_append,listCells_under,listCells] at hl hd ⊢
  omega

def uniform (input : Input) (mirror : SignedWord) : ℕ :=
  let prepared := BinaryNestedSecondUniformMeasured.prepare input mirror
  let child := BinaryThreeFactoryMeasured.ordered prepared.1.1
  BinaryArithmeticEntryWork.raw .sub input.M mirror+BinaryArithmeticEntryWork.raw .sub input.t mirror+
    BinaryThreeFactoryArithmeticEntryWork.ordered prepared.1.1+shift child.1.1 mirror

theorem uniform_bound (input : Input) (mirror : SignedWord) :
    uniform input mirror ≤ 2*listCells (BinaryNestedSecondUniformMeasured.uniform input mirror).1.2 := by
  have hb := quadratic_bound .sub input.M mirror
  have hl := quadratic_bound .sub input.t mirror
  have hc := BinaryThreeFactoryArithmeticEntryWork.ordered_bound (BinaryNestedSecondUniformMeasured.prepare input mirror).1.1
  have hs := shift_bound (BinaryThreeFactoryMeasured.ordered (BinaryNestedSecondUniformMeasured.prepare input mirror).1.1).1.1 mirror
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,uniform,BinaryNestedSecondUniformMeasured.uniform_record,BinaryNestedSecondUniformMeasured.fromPrepared_record,
    BinaryNestedSecondUniformMeasured.collect,BinaryNestedSecondUniformMeasured.prepare_record,BinaryNestedSecondUniformMeasured.collectInput,
    wrap,combine,listCells_append,listCells_under,listCells] at hc hs ⊢
  omega

def weights (p q : SignedWord) (first second : FixedArrayTable 9 SignedWord) : ℕ :=
  tableCost 18 (fun slot => Fin.addCases (n := 9)
    (fun j => BinaryArithmeticEntryWork.raw .mul p (first.read j))
    (fun j => BinaryArithmeticEntryWork.raw .mul q (second.read j)) slot)

theorem weights_bound (p q : SignedWord) (first second : FixedArrayTable 9 SignedWord) :
    weights p q first second ≤ 2*listCells (BinaryNestedBinaryAssemblyMeasured.weights p q first second).1.2 := by
  simp only [BinaryNestedBinaryAssemblyMeasured.weights_record,BinaryPlannedQuadratic.apply_previous]
  apply build_bound 18
  intro slot
  refine Fin.addCases (m := 9) (n := 9) (fun j => ?_) (fun j => ?_) slot
  · simp only [Fin.addCases_left]; exact quadratic_bound .mul _ _
  · simp only [Fin.addCases_right]; exact quadratic_bound .mul _ _

def binary (p : SignedWord) (first second : Small) : ℕ :=
  let complement := BinaryQuadraticMeasured.apply .sub BinaryExpressionCompiler.Constant.one.word p
  BinaryArithmeticEntryWork.raw .sub BinaryExpressionCompiler.Constant.one.word p+weights p complement.1.1 first.weight second.weight

theorem binary_bound (p : SignedWord) (first second : Small) :
    binary p first second ≤ 2*listCells (BinaryNestedBinaryAssemblyMeasured.binary p first second).1.2 := by
  have hc := quadratic_bound .sub BinaryExpressionCompiler.Constant.one.word p
  have hw := weights_bound p (BinaryQuadraticMeasured.apply .sub BinaryExpressionCompiler.Constant.one.word p).1.1 first.weight second.weight
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,binary,BinaryNestedBinaryAssemblyMeasured.binary_record,BinaryNestedBinaryAssemblyMeasured.fromComplement_record,
    BinaryNestedBinaryAssemblyMeasured.collect,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def second (input : Input) (parameters : FixedArrayTable 9 SignedWord) (K : ℕ) (bits : BinaryScalarTape K) : ℕ :=
  let selected := BinaryNestedFamilyMeasured.selected input parameters K bits
  let guard := BinaryQuadraticExpressionMeasured.compare input.t (parameters.read 6)
  family input (parameters.read 6) K bits+BinaryArithmeticEntryWork.comparison input.t (parameters.read 6)+
    if !guard.1.1 then uniform input (parameters.read 6)+
      binary (parameters.read 7) selected.1.1 (BinaryNestedSecondUniformMeasured.selected input parameters).1.1 else 0

theorem second_bound (input : Input) (parameters : FixedArrayTable 9 SignedWord) (K : ℕ) (bits : BinaryScalarTape K) :
    second input parameters K bits ≤ 2*listCells (BinaryNestedSecondProfileMeasured.profile input parameters K bits).1.2 := by
  have hf := family_bound input (parameters.read 6) K bits
  have hg := comparison_bound input.t (parameters.read 6)
  have hu := uniform_bound input (parameters.read 6)
  have hb := binary_bound (parameters.read 7) (BinaryNestedFamilyMeasured.lottery input (parameters.read 6) K bits).1.1
    (BinaryNestedSecondUniformMeasured.uniform input (parameters.read 6)).1.1
  simp only [second,BinaryNestedSecondProfileMeasured.profile_record,BinaryNestedSecondProfileMeasured.finish,
    BinaryNestedFamilyMeasured.selected,BinaryNestedSecondUniformMeasured.selected]
  generalize hFamily : BinaryNestedFamilyMeasured.lottery input (parameters.read 6) K bits = returnedFamily at hf hb ⊢
  generalize hUniform : BinaryNestedSecondUniformMeasured.uniform input (parameters.read 6) = returnedUniform at hu hb ⊢
  generalize hGuard : BinaryQuadraticExpressionMeasured.compare input.t (parameters.read 6) = returnedGuard at hg ⊢
  split_ifs <;> simp only [BinaryNestedSecondProfileMeasured.mix_record,wrap,combine,listCells_append,listCells_under,listCells] <;> omega


def residualWeights (env : FixedArrayTable 5 SignedWord) : ℕ := tableCost 3 (fun j => compiledCost env (BinaryNestedResidualCompiler.weights j))

theorem residualWeights_bound (env : FixedArrayTable 5 SignedWord) :
    residualWeights env ≤ 2*listCells (BinaryNestedResidualDescriptorMeasured.weights env).1.2 := by
  rw [BinaryNestedResidualDescriptorMeasured.weights_record]
  exact (
    build_bound 3 _ _ (fun _j => compiled_bound _ _)
  )

def residualVertex (env : FixedArrayTable 5 SignedWord) (vertex : Fin 3) : ℕ := tableCost 3 (fun j => compiledCost env (BinaryNestedResidualCompiler.vertices vertex j))

theorem residualVertex_bound (env : FixedArrayTable 5 SignedWord) (vertex : Fin 3) :
    residualVertex env vertex ≤ 2*listCells (BinaryNestedResidualDescriptorMeasured.vertexRow env vertex).1.2 := by
  rw [BinaryNestedResidualDescriptorMeasured.vertexRow_record]
  exact (
    build_bound 3 _ _ (fun _j => compiled_bound _ _)
  )

def residualRows (env : FixedArrayTable 5 SignedWord) (edge : Fin 3 → Fin 3) : ℕ := tableCost 3 (fun slot => residualVertex env (edge slot))

theorem residualRows_bound (env : FixedArrayTable 5 SignedWord) (edge : Fin 3 → Fin 3) :
    residualRows env edge ≤ 2*listCells (BinaryNestedResidualDescriptorMeasured.rows env edge).1.2 := by
  rw [BinaryNestedResidualDescriptorMeasured.rows_record]
  exact (
    build_bound 3 _ _ (fun _slot => residualVertex_bound _ _)
  )

def residualDescriptor (env : FixedArrayTable 5 SignedWord) : ℕ := residualWeights env+
  residualRows env (fun slot => (RationalNestedResidual.edges slot).1)+residualRows env (fun slot => (RationalNestedResidual.edges slot).2)

theorem residualDescriptor_bound (env : FixedArrayTable 5 SignedWord) :
    residualDescriptor env ≤ 2*listCells (BinaryNestedResidualDescriptorMeasured.descriptor env).1.2 := by
  have hw := residualWeights_bound env
  have hp := residualRows_bound env (fun slot => (RationalNestedResidual.edges slot).1)
  have hq := residualRows_bound env (fun slot => (RationalNestedResidual.edges slot).2)
  simp only [residualDescriptor,BinaryNestedResidualDescriptorMeasured.descriptor_record,wrap,combine,listCells_append,listCells_under,listCells]
  omega

def residual (input : Input) (parameters : FixedArrayTable 9 SignedWord) : ℕ :=
  BinaryArithmeticEntryWork.raw .sub input.M input.c+residualDescriptor (BinaryNestedResidualMeasured.environment input parameters).1.1

theorem residual_bound (input : Input) (parameters : FixedArrayTable 9 SignedWord) :
    residual input parameters ≤ 2*listCells (BinaryNestedResidualMeasured.residual input parameters).1.2 := by
  have he := quadratic_bound .sub input.M input.c
  have hd := residualDescriptor_bound (BinaryNestedResidualMeasured.environment input parameters).1.1
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,residual,BinaryNestedResidualMeasured.residual_record,BinaryNestedResidualMeasured.fromEnvironment_record,
    BinaryNestedResidualMeasured.environment_record,BinaryNestedResidualMeasured.environmentFrom,
    wrap,combine,listCells_append,listCells_under,listCells] at hd ⊢
  omega

def third (input : Input) (parameters : FixedArrayTable 9 SignedWord) (K : ℕ) (bits : BinaryScalarTape K) : ℕ :=
  let produced := BinaryNestedResidualMeasured.residual input parameters
  let padded := BinaryNestedResidualMeasured.pad produced.1.1
  let guard := BinaryQuadraticExpressionMeasured.compare (parameters.read 2) BinaryRationalOpcode.zero
  residual input parameters+BinaryArithmeticEntryWork.comparison (parameters.read 2) BinaryRationalOpcode.zero+
    if !guard.1.1 then family input (parameters.read 2) K bits+
      binary (parameters.read 8) (BinaryNestedFamilyMeasured.lottery input (parameters.read 2) K bits).1.1 padded.1.1 else 0

theorem third_bound (input : Input) (parameters : FixedArrayTable 9 SignedWord) (K : ℕ) (bits : BinaryScalarTape K) :
    third input parameters K bits ≤ 2*listCells (BinaryNestedThirdProfileMeasured.profile input parameters K bits).1.2 := by
  have hr := residual_bound input parameters
  have hg := comparison_bound (parameters.read 2) BinaryRationalOpcode.zero
  have hf := family_bound input (parameters.read 2) K bits
  have hb := binary_bound (parameters.read 8) (BinaryNestedFamilyMeasured.lottery input (parameters.read 2) K bits).1.1
    (BinaryNestedResidualMeasured.pad (BinaryNestedResidualMeasured.residual input parameters).1.1).1.1
  simp only [third,BinaryNestedThirdProfileMeasured.profile_record,BinaryNestedThirdProfileMeasured.finish]
  split_ifs <;> simp only [BinaryNestedThirdProfileMeasured.mix_record,wrap,combine,listCells_append,listCells_under,listCells] <;> omega

def ordered (input : Input) (parameters : FixedArrayTable 9 SignedWord) (regime : Fin 3) (K : ℕ) (bits : BinaryScalarTape K) : ℕ :=
  if regime=0 then first input K bits else if regime=1 then second input parameters K bits else third input parameters K bits

theorem ordered_bound (input : Input) (parameters : FixedArrayTable 9 SignedWord) (regime : Fin 3) (K : ℕ) (bits : BinaryScalarTape K) :
    ordered input parameters regime K bits ≤ 2*listCells (BinaryNestedProfileMeasured.ordered input parameters regime K bits).1.2 := by
  have h0 := first_bound input K bits
  have h1 := second_bound input parameters K bits
  have h2 := third_bound input parameters K bits
  simp only [ordered,BinaryNestedProfileMeasured.ordered_record]
  split_ifs <;> simp only [BinaryNestedProfileMeasured.retain,wrap,combine,listCells_append,listCells_under,listCells] <;> omega

def profile (input : Input) (K : ℕ) (bits : BinaryScalarTape K) : ℕ := control input+
  match (BinaryNestedControlMeasured.run input).1.1 with
  | Sum.inl _ => 0
  | Sum.inr selected => ordered selected.1.1.1 selected.1.2 selected.2 K bits

theorem profile_bound (input : Input) (K : ℕ) (bits : BinaryScalarTape K) :
    profile input K bits ≤ 2*listCells (BinaryNestedProfileMeasured.profile input K bits).1.2 := by
  have hc := control_bound input
  simp only [profile,BinaryNestedProfileMeasured.profile_record]
  cases h : (BinaryNestedControlMeasured.run input).1.1 with
  | inl table => simp only [wrap,combine,listCells_append,listCells_under,listCells]; omega
  | inr selected =>
    have ho := ordered_bound selected.1.1.1 selected.1.2 selected.2 K bits
    simp only [BinaryNestedReferenceMeasured.restore]
    split <;> simp only [wrap,combine,listCells_append,listCells_under,listCells] <;> omega

theorem profile_input_bound (input : Input) (hC : input.Canonical) (s : ℕ) (hs : 3 ≤ s)
    (hH : BinaryNestedParameterWork.InputHeight input s) (K : ℕ) (bits : BinaryScalarTape K) :
    profile input K bits ≤ 2*BinaryNestedProfileMeasured.envelope s K := by
  have he := profile_bound input K bits
  have hu := (BinaryNestedProfileMeasured.profile_bounds input hC s hs hH K bits).2
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells at hu
  omega

end Blotto.BinaryNestedProfileArithmeticEntryWork
