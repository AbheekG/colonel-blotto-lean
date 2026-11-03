import Blotto.GeneralPaperArithmeticDriverWork

/-! Sharp full real-RAM driver time. Compiler/source summands keep their
field/accuracy tradeoffs until the actual reduced-field cap is applied.
Unused original-ratio encoding logs are removed only from analysis bounds. -/
namespace Blotto.GeneralPaperArithmeticDriverSharpTime
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra GeneralPaperNativeSourceRates
open GeneralPaperConstructedWordGrowth GeneralPaperArithmeticCompilerWork
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384

def realRate (x : Input) : ℕ := monomial 4 0 3 x+GeneralPaperSourceCallerSharpWork.realRate x

theorem embed {f : Input → ℕ} {a c : ℕ} (h : Rated f a 0 c)
    (fits : (a≤4 ∧ c≤3) ∨ (a≤3 ∧ c≤4) ∨ (a≤2 ∧ c≤5)) : Soft realRate f := by
  rcases fits with h0|h1|h2
  · apply rate_mono (weaken h h0.1 le_rfl h0.2)
    intro x
    unfold realRate
    omega
  · apply rate_mono (weaken h h1.1 le_rfl h1.2)
    intro x
    unfold realRate GeneralPaperSourceCallerSharpWork.realRate
    omega
  · apply rate_mono (weaken h h2.1 le_rfl h2.2)
    intro x
    unfold realRate GeneralPaperSourceCallerSharpWork.realRate
    omega

open Lean Meta Elab Tactic in
elab "source_real_time" : tactic => withMainContext do
  let main ← getMainGoal
  let target ← instantiateMVars (← main.getType)
  unless target.isAppOf ``GeneralPaperSourceSoftBounds.Soft do
    throwError "source_real_time expects a Soft goal, saw {target.getAppFn}"
  let fn := target.getAppArgs[1]!
  lambdaTelescope fn fun xs body => do
    unless xs.size == 1 do throwError "source_real_time expects one input"
    let x := xs[0]!
    let close := fun e => mkLambdaFVars #[x] e
    let rec build : Nat → Expr → TacticM Expr
      | 0,_ => throwError "source_real_time structural depth exceeded"
      | fuel+1,e => do
        let e ← instantiateMVars e
        let name := e.getAppFn.constName?
        let args := e.getAppArgs
        if name == some ``HAdd.hAdd || name == some ``Nat.add then
          let p ← build fuel args[args.size-2]!
          let q ← build fuel args.back!
          return ← mkAppM ``GeneralPaperSourceSoftBounds.add_same #[p,q]
        let f ← close e
        let a ← mkFreshExprMVar (mkConst ``Nat)
        let b ← mkFreshExprMVar (mkConst ``Nat)
        let c ← mkFreshExprMVar (mkConst ``Nat)
        let ty ← mkAppM ``GeneralPaperSourceRateAlgebra.Rated #[f,a,b,c]
        let g ← mkFreshExprMVar ty
        let old ← getGoals
        setGoals [g.mvarId!]
        try
          evalTactic (← `(tactic| source_space))
          unless (← getGoals).isEmpty do throwError "unclosed source_real_time summand"
          let some av ← getNatValue? (← whnf (← instantiateMVars a)) | throwError "nonliteral field degree"
          let some bv ← getNatValue? (← whnf (← instantiateMVars b)) | throwError "nonliteral alphabet degree"
          let some cv ← getNatValue? (← whnf (← instantiateMVars c)) | throwError "nonliteral accuracy degree"
          unless bv == 0 && ((av ≤ 4 && cv ≤ 3) || (av ≤ 3 && cv ≤ 4) || (av ≤ 2 && cv ≤ 5)) do
            throwError "source_real_time summand has degrees ({av},{bv},{cv}): {e}"
          let proof ← instantiateMVars g
          let embedded ← mkAppM ``Blotto.GeneralPaperArithmeticDriverSharpTime.embed #[proof]
          let ty ← whnf (← inferType embedded)
          let .forallE _ fitType _ _ := ty | throwError "source_real_time missing degree condition"
          let fit ← mkFreshExprMVar fitType
          setGoals [fit.mvarId!]
          evalTactic (← `(tactic| decide))
          return ← instantiateMVars (mkApp embedded fit)
        finally
          setGoals old
    let proof ← build 512 body
    main.assign proof
    replaceMainGoal []

theorem input_word_rate : Rated (fun x => inputWord x.m x.k) 1 0 1 := by
  have hH := GeneralPaperBasisStorageRates.determinant_length
  have hCap := GeneralPaperSourceSharpOperandRates.cap_word
  change Rated (fun x => binaryWordWidth (4*x.m*(GeneralPaperProxyParameters.prepare x.m x.k).H*
    (GeneralPaperProxyParameters.prepare x.m x.k).qbar*(GeneralPaperProxyParameters.prepare x.m x.k).qbar)) 1 0 1
  source_space

theorem compiler_rate : Soft realRate (fun x => GeneralPaperArithmeticCompilerWork.price x.m x.k) := by
  have hRows := GeneralPaperSourceStaticConstructionRates.sharp_rows
  have hi := input_word_rate
  dsimp only [GeneralPaperArithmeticCompilerWork.price,modifiedPrice,branchPrice,strictPrice,endpointPrice,
    inputPrice,basisPrice,checkPrice,columnsPrice,GeneralPaperRetainedTransferPrice.arithmeticProfile,
    GeneralPaperEndpointPriceControl.profile,GeneralPaperHighSearchPriceFacts.profile,
    GeneralPaperHighSearchPriceControl.profile,GeneralPaperParametricPriceProfiles.profile,
    GeneralPaperFinalRefinementPrice.profile,GeneralPaperHighBlockerPrice.profile,
    GeneralPaperFinalRefinementPrice.envelope,GeneralPaperFixedViolationPrice.profile,
    GeneralPaperParametricRecursionPrice.profile,GeneralPaperParametricStageBits.profile,
    GeneralPaperAffineStepPrice.profile]
  simp only [Nat.add_mul,Nat.mul_add,Nat.add_assoc]
  change Soft realRate _
  source_real_time

def preparationCertificate : Certificate (fun x => GeneralPaperArithmeticPairPreparation.profile x.m x.k x.Qv) := by
  have hL := GeneralPaperSourceSharpOperandRates.alphabet_length
  have hH := GeneralPaperBasisStorageRates.determinant_length
  have hCap := GeneralPaperSourceSharpOperandRates.cap_word
  have hGrid := GeneralPaperSourceEndpointFractionConstructionStorageRates.grid_word_sharp
  have hGB := GeneralPaperFastDriverSharpWork.grid_bits_rate
  have hD := GeneralPaperFastFrontStorageRates.comparator_order_word
  refine ⟨_,_,_,by
    dsimp only [GeneralPaperArithmeticPairPreparation.profile,GeneralPaperArithmeticSourcePrecall.profile,
      GeneralPaperPrecallCachePrice.profile,GeneralPaperProxyParameterPrice.profile,GeneralPaperScoreScalePrice.profile,
      GeneralPaperQuadraticGridPrice.profile,GeneralPaperComparatorParameterPrice.profile,
      GeneralPaperProfitGridProfile.bound,GeneralPaperProfitGridProfile.sizeFactor,GeneralPaperProfitGridProfile.logFactor,
      GeneralPaperProfitGridPrice.count]
    source_space⟩

def preparationSubstitution : Certificate (fun x => monomial preparationCertificate.fields
    preparationCertificate.symbols preparationCertificate.accuracy x) := by
  have hL := GeneralPaperSourceSharpOperandRates.alphabet_length
  have hAcc : Rated (fun x => 2^x.k) 0 0 1 := by simpa only [Nat.zero_add] using dyadic_accuracy 0
  refine ⟨_,_,_,by
    unfold monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
    source_space⟩

theorem preparation_degrees :
    (preparationSubstitution.fields,preparationSubstitution.symbols,preparationSubstitution.accuracy)=(2,0,2) := rfl

theorem preparation_rate : Soft realRate (fun x => GeneralPaperArithmeticPairPreparation.profile x.m x.k x.Qv) := by
  apply embed (GeneralPaperSourceCallerSharpWork.soft_trans preparationSubstitution.bound preparationCertificate.bound)
  decide

theorem lift_source {f : Input → ℕ} (h : Soft GeneralPaperSourceCallerSharpWork.realRate f) : Soft realRate f :=
  rate_mono h (fun _x => Nat.le_add_left _ _)

theorem rate_positive (x : Input) : 1≤realRate x := (monomial_positive 4 0 3 x).trans (Nat.le_add_right _ _)

theorem price_rate : Soft realRate (fun x => GeneralPaperArithmeticDriverWork.price x.m x.k x.Qv) := by
  have hSource := lift_source GeneralPaperArithmeticUnitSourceWork.source_rate
  have hValues : Soft realRate (fun x => 79*x.m+237) := by
    apply embed
    · source_space
    · decide
  have hc (n : ℕ) : Soft realRate (fun _ => n) := poly_at_rate (poly_constant n) rate_positive
  have hPrepared := add_same (add_same (add_same hValues (poly_mul_rate (poly_constant 2) hSource)) compiler_rate) (hc 128)
  have hCached := add_same (add_same (add_same (hc 256) (hc 256)) hPrepared) (hc 128)
  exact add_same (add_same preparation_rate hCached) (hc 64)

theorem core_bound : ∃ A e : ℕ,∀ x,GeneralPaperArithmeticDriverWork.price x.m x.k x.Qv≤
    A*realRate x*(GeneralPaperSourceCoreLogBound.coreLog x)^e :=
  GeneralPaperSourceCoreLogBound.remove_unused_height price_rate (fun _ => rfl) (fun _ => rfl)

theorem collapse (x : Input) (cap : ℕ) (h : x.m≤cap*accuracy x) :
    realRate x≤((cap+1)^2+cap+2)*monomial 2 0 5 x := by
  have hf := GeneralPaperSourceCallerSharpWork.reduced_field_bound x cap h
  have h0 := GeneralPaperSourceCallerSharpWork.field_shift x (cap+1) 3 3 hf
  have h1 := GeneralPaperSourceCallerSharpWork.field_shift x (cap+1) 2 4 hf
  have h2 := GeneralPaperSourceCallerSharpWork.real_collapse x cap h
  have hTop := h0.trans (Nat.mul_le_mul_left (cap+1) h1)
  unfold realRate
  calc
    monomial 4 0 3 x+GeneralPaperSourceCallerSharpWork.realRate x≤
      (cap+1)*((cap+1)*monomial 2 0 5 x)+(cap+2)*monomial 2 0 5 x := Nat.add_le_add hTop h2
    _=((cap+1)^2+cap+2)*monomial 2 0 5 x := by ring

theorem real_time (model : RationalCostModel) (cap : ℕ) :
    ∃ A e : ℕ,∀ (x : Input) (_hm : 0<x.m) (hQv : 0<x.Qv) (hp : ∀ j,0<x.weights.read j),x.m≤cap*accuracy x →
      ∀ (b : ℝ),0<b ∧ b<1 →
      (GeneralPaperArithmeticSourcePairDriver.run model x.k x.Qv hQv x.weights hp x.weight_sum b).2≤
        A*monomial 2 0 5 x*(GeneralPaperSourceCoreLogBound.coreLog x)^e := by
  obtain ⟨A,e,h⟩ := core_bound
  refine ⟨A*((cap+1)^2+cap+2),e,?_⟩
  intro x hm hQv hp hCap b hb
  exact (GeneralPaperArithmeticDriverWork.work model x.k x.Qv hm hQv x.weights hp x.weight_sum b hb).trans
    ((h x).trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left A (collapse x cap hCap))).trans_eq (by ring)))

theorem real_time_and_return (model : RationalCostModel) (cap : ℕ) :
    ∃ A e : ℕ,∀ (x : Input) (_hm : 0<x.m) (hQv : 0<x.Qv) (hp : ∀ j,0<x.weights.read j),x.m≤cap*accuracy x →
      ∀ (b : ℝ),0<b ∧ b<1 →
      ∃ physical pair,(GeneralPaperArithmeticSourcePairDriver.run model x.k x.Qv hQv x.weights hp x.weight_sum b).1=some physical ∧
        GeneralPaperSourcePairRun.run x.k x.Qv hQv x.weights hp x.weight_sum b=some pair ∧
        GeneralPaperOriginalDrawEquilibrium.Matches physical pair ∧
        GeneralPaperSourcePairContract.Contract x.k x.Qv hQv x.weights hp x.weight_sum b pair ∧
        (GeneralPaperArithmeticSourcePairDriver.run model x.k x.Qv hQv x.weights hp x.weight_sum b).2≤
          A*monomial 2 0 5 x*(GeneralPaperSourceCoreLogBound.coreLog x)^e := by
  obtain ⟨A,e,h⟩ := real_time model cap
  refine ⟨A,e,?_⟩
  intro x hm hQv hp hCap b hb
  obtain ⟨physical,pair,hRun,hPair,hMatches,hContract⟩ := GeneralPaperArithmeticSourcePairDriver.actual_return model
    x.k x.Qv hm hQv x.weights hp x.weight_sum b hb
  exact ⟨physical,pair,hRun,hPair,hMatches,hContract,h x hm hQv hp hCap b hb⟩

theorem actual_time (model : RationalCostModel) (cap : ℕ) :
    ∃ A e : ℕ,∀ (x : Input) (_hm : 0<x.m) (hQv : 0<x.Qv) (hp : ∀ j,0<x.weights.read j),x.m≤cap*accuracy x →
      (GeneralPaperArithmeticSourcePairDriver.run model x.k x.Qv hQv x.weights hp x.weight_sum (x.b:ℝ)).2≤
        A*monomial 2 0 5 x*(GeneralPaperSourceCoreLogBound.coreLog x)^e := by
  obtain ⟨A,e,h⟩ := core_bound
  refine ⟨A*((cap+1)^2+cap+2),e,?_⟩
  intro x hm hQv hp hCap
  have hb : 0<(x.b:ℝ) ∧ (x.b:ℝ)<1 := by exact_mod_cast x.hb
  exact (GeneralPaperArithmeticDriverWork.work model x.k x.Qv hm hQv x.weights hp x.weight_sum (x.b:ℝ) hb).trans
    ((h x).trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left A (collapse x cap hCap))).trans_eq (by ring)))

theorem time_and_return (model : RationalCostModel) (cap : ℕ) :
    ∃ A e : ℕ,∀ (x : Input) (_hm : 0<x.m) (hQv : 0<x.Qv) (hp : ∀ j,0<x.weights.read j),x.m≤cap*accuracy x →
      ∃ physical pair,(GeneralPaperArithmeticSourcePairDriver.run model x.k x.Qv hQv x.weights hp x.weight_sum (x.b:ℝ)).1=some physical ∧
        GeneralPaperSourcePairRun.run x.k x.Qv hQv x.weights hp x.weight_sum (x.b:ℝ)=some pair ∧
        GeneralPaperOriginalDrawEquilibrium.Matches physical pair ∧
        GeneralPaperSourcePairContract.Contract x.k x.Qv hQv x.weights hp x.weight_sum (x.b:ℝ) pair ∧
        (GeneralPaperArithmeticSourcePairDriver.run model x.k x.Qv hQv x.weights hp x.weight_sum (x.b:ℝ)).2≤
          A*monomial 2 0 5 x*(GeneralPaperSourceCoreLogBound.coreLog x)^e := by
  obtain ⟨A,e,h⟩ := actual_time model cap
  refine ⟨A,e,?_⟩
  intro x hm hQv hp hCap
  have hb : 0<(x.b:ℝ) ∧ (x.b:ℝ)<1 := by exact_mod_cast x.hb
  obtain ⟨physical,pair,hRun,hPair,hMatches,hContract⟩ := GeneralPaperArithmeticSourcePairDriver.actual_return model
    x.k x.Qv hm hQv x.weights hp x.weight_sum (x.b:ℝ) hb
  exact ⟨physical,pair,hRun,hPair,hMatches,hContract,h x hm hQv hp hCap⟩

end Blotto.GeneralPaperArithmeticDriverSharpTime
