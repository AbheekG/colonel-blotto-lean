import Blotto.GeneralPaperParameterScalarStorage

/-! Native source-control scalar construction: the fixed primitive fields
outside dyadic/ceiling children, all returned/temporary records, selected
recursive children and parent cost metadata. Powers/grid are not executed
in this parameter phase. Observers erase and use actual-return identities. -/
namespace Blotto.GeneralPaperSourceControlsConstructionStorage
open GeneralPaperParameterScalarStorage GeneralPaperEncodedScalarStorage
open GeneralPaperScoreScaleParameters
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def indices (k : ℕ) : List NaturalOp :=
  [((·+·),11,k),((·+·),25,k),((·+·),32,k),((·+·),29,k),((·+·),34,k)]

def trajectory (lambda k period factor epochs depth periodDepth : ℕ) : List NaturalOp :=
  [((·+·),35,k),((·+·),lambda,2),((·*·),lambda+2,factor),((·*·),epochs,period),((·+·),depth,periodDepth)]

def profit (Qv rows mesh height alpha : ℕ) : List NaturalOp :=
  [((·*·),2,rows),((·*·),2*rows,Qv),((·*·),2*rows*Qv,mesh),((·+·),height,1),
    ((·*·),4,height+1),((·*·),4*(height+1),alpha),((·*·),4,2*rows*Qv*mesh)]

def precision (lambda k rows mesh nu : ℕ) : List NaturalOp :=
  let G := GeneralPaperPrecisionParameterPrice.level rows mesh
  let E := GeneralPaperPrecisionParameterPrice.error lambda rows mesh
  [((·*·),8,rows),((·*·),8*rows,mesh),((·+·),G,1),((·+·),lambda,2),((·*·),16,G+1),
    ((·*·),16*(G+1),lambda+2),((·*·),2,k),((·+·),74,2*k),((·*·),64,E),((·*·),64*E,nu)]

def ops (m lambda k Qv : ℕ) : List NaturalOp :=
  let s := GeneralPaperSourceParameters.prepare k
  let t := GeneralPaperTrajectoryParameters.prepare lambda k
  let p := powerRun (11+k)
  let f := powerRun (35+k)
  let e := GeneralPaperPowerCeiling.ceiling (GeneralPaperTrajectoryParameterPrice.target lambda k)
  indices k++trajectory lambda k p.power f.power e.power e.doublings p.doublings++
    profit Qv t.rows s.meshDenominator (GeneralPaperPowerCeiling.ceiling m).doublings (powerRun (25+k)).power++
    precision lambda k t.rows s.meshDenominator (powerRun (32+k)).power

def charges (model : RationalCostModel) (m lambda k Qv : ℕ) : List ℕ :=
  let s := GeneralPaperSourceParameters.prepare k
  let t := GeneralPaperTrajectoryParameters.prepare lambda k
  let nu := (powerRun (32+k)).power
  let minimum := (powerRun (74+2*k)).power
  (indices k).map (opCost model)++
    [GeneralPaperSourceParameterPrice.inverseCost model.rat (powerRun (11+k)).power,
      GeneralPaperSourceParameterPrice.inverseCost model.rat (powerRun (25+k)).power,
      GeneralPaperSourceParameterPrice.inverseCost model.rat (powerRun (32+k)).power,
      GeneralPaperSourceParameterPrice.inverseCost model.rat (powerRun (29+k)).power]++
    (trajectory lambda k (powerRun (11+k)).power (powerRun (35+k)).power
      (GeneralPaperPowerCeiling.ceiling (GeneralPaperTrajectoryParameterPrice.target lambda k)).power
      (GeneralPaperPowerCeiling.ceiling (GeneralPaperTrajectoryParameterPrice.target lambda k)).doublings (powerRun (11+k)).doublings++
      profit Qv t.rows s.meshDenominator (GeneralPaperPowerCeiling.ceiling m).doublings (powerRun (25+k)).power++
      precision lambda k t.rows s.meshDenominator nu).map (opCost model)++[
      GeneralPaperIntegerWordPrice.compare model.rat minimum (64*GeneralPaperPrecisionParameterPrice.error lambda t.rows s.meshDenominator*nu),
      model.rat (natBits (GeneralPaperPrecisionParameterPrice.target lambda t.rows s.meshDenominator nu minimum))]

def rawCost (model : RationalCostModel) (m lambda k Qv : ℕ) : ℕ := (charges model m lambda k Qv).sum

theorem lengths (model : RationalCostModel) (m lambda k Qv : ℕ) :
    (ops m lambda k Qv).length=27 ∧ (charges model m lambda k Qv).length=33 := by
  simp only [ops,indices,trajectory,profit,precision,charges,List.length_append,List.length_map,List.length_cons,List.length_nil,and_self]

theorem cost_data (model : RationalCostModel) (m lambda k Qv : ℕ) :
    rawCost model m lambda k Qv=
      GeneralPaperSourceParameterPrice.indexCost model.rat k+
      GeneralPaperSourceParameterPrice.inverseCost model.rat (powerRun (11+k)).power+
      GeneralPaperSourceParameterPrice.inverseCost model.rat (powerRun (25+k)).power+
      GeneralPaperSourceParameterPrice.inverseCost model.rat (powerRun (32+k)).power+
      GeneralPaperSourceParameterPrice.inverseCost model.rat (powerRun (29+k)).power+
      GeneralPaperTrajectoryParameterPrice.rawWork model.rat lambda k (powerRun (11+k)).power (powerRun (35+k)).power
        (GeneralPaperPowerCeiling.ceiling (GeneralPaperTrajectoryParameterPrice.target lambda k)).power
        (GeneralPaperPowerCeiling.ceiling (GeneralPaperTrajectoryParameterPrice.target lambda k)).doublings (powerRun (11+k)).doublings+
      GeneralPaperProfitParameterPrice.rawWork model.rat Qv (GeneralPaperTrajectoryParameters.prepare lambda k).rows
        (GeneralPaperSourceParameters.prepare k).meshDenominator (GeneralPaperPowerCeiling.ceiling m).doublings (powerRun (25+k)).power+
      GeneralPaperPrecisionParameterPrice.rawWork model.rat lambda k (GeneralPaperTrajectoryParameters.prepare lambda k).rows
        (GeneralPaperSourceParameters.prepare k).meshDenominator (powerRun (32+k)).power (powerRun (74+2*k)).power := by
  dsimp only [rawCost,charges,ops,indices,trajectory,profit,precision,opCost,GeneralPaperSourceParameterPrice.indexCost,
    GeneralPaperTrajectoryParameterPrice.rawWork,GeneralPaperProfitParameterPrice.rawWork,GeneralPaperPrecisionParameterPrice.rawWork,
    GeneralPaperNaturalPrimitivePrice.word,natBits,List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil]
  simp only [List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,opCost]
  omega

theorem raw_bound (model : RationalCostModel) (m lambda k Qv : ℕ) :
    rawCost model m lambda k Qv≤68*model.rat (GeneralPaperSourcePreparationSizes.width m lambda k Qv) := by
  let H := GeneralPaperSourcePreparationSizes.width m lambda k Qv
  have hs := GeneralPaperSourcePreparationSizes.sizes m lambda k Qv
  have hi := GeneralPaperSourceParameterPrice.indices_work model.rat model.monotone k
  have hz := GeneralPaperSourceParameterPrice.dyadic_inverse_work model.rat model.monotone k 11 (by decide)
  have he := GeneralPaperSourceParameterPrice.dyadic_inverse_work model.rat model.monotone k 25 (by decide)
  have hn := GeneralPaperSourceParameterPrice.dyadic_inverse_work model.rat model.monotone k 32 (by decide)
  have ht := GeneralPaperSourceParameterPrice.dyadic_inverse_work model.rat model.monotone k 29 (by decide)
  have hT := GeneralPaperTrajectoryParameterPrice.raw_work model.rat model.monotone lambda k (powerRun (11+k)).power (powerRun (35+k)).power
    (GeneralPaperPowerCeiling.ceiling (GeneralPaperTrajectoryParameterPrice.target lambda k)).power
    (GeneralPaperPowerCeiling.ceiling (GeneralPaperTrajectoryParameterPrice.target lambda k)).doublings (powerRun (11+k)).doublings
  have hP := GeneralPaperProfitParameterPrice.raw_work model.rat model.monotone m Qv (GeneralPaperTrajectoryParameters.prepare lambda k).rows
    (GeneralPaperSourceParameters.prepare k).meshDenominator (GeneralPaperPowerCeiling.ceiling m).doublings (powerRun (25+k)).power
  have hF := GeneralPaperPrecisionParameterPrice.raw_work model.rat model.monotone lambda k (GeneralPaperTrajectoryParameters.prepare lambda k).rows
    (GeneralPaperSourceParameters.prepare k).meshDenominator (powerRun (32+k)).power (powerRun (74+2*k)).power
  have hSW := model.monotone hs.source
  have hTW := model.monotone hs.trajectoryRaw
  have hPW := model.monotone hs.profitRaw
  have hFW := model.monotone hs.precisionRaw
  rw [cost_data]
  omega

def rawWindow (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  let s := GeneralPaperSourceParameters.prepare k
  let t := GeneralPaperTrajectoryParameters.prepare lambda k
  let nu := (powerRun (32+k)).power
  let minimum := (powerRun (74+2*k)).power
  GeneralPaperParameterScalarStorage.window model W (ops m lambda k Qv)+
    inverseWindow model W (powerRun (11+k)).power+inverseWindow model W (powerRun (25+k)).power+
    inverseWindow model W (powerRun (32+k)).power+inverseWindow model W (powerRun (29+k)).power+
    compareWindow model W minimum (64*GeneralPaperPrecisionParameterPrice.error lambda t.rows s.meshDenominator*nu)+
    writeWindow model W (GeneralPaperPrecisionParameterPrice.target lambda t.rows s.meshDenominator nu minimum)+
    priceFields W (charges model m lambda k Qv)+1024*W

def rawProfile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  let P := model.rat (GeneralPaperSourcePreparationSizes.width m lambda k Qv)
  544*P+33*(192*W+16)+67*(natBits (68*P)+W)+1056*W

theorem raw_window_bound (model : RationalCostModel) (W m lambda k Qv : ℕ) :
    rawWindow model W m lambda k Qv≤rawProfile model W m lambda k Qv := by
  have hOps := list_bound model W (ops m lambda k Qv)
  have hz := inverse_bound model W (powerRun (11+k)).power
  have he := inverse_bound model W (powerRun (25+k)).power
  have hn := inverse_bound model W (powerRun (32+k)).power
  have ht := inverse_bound model W (powerRun (29+k)).power
  have hc := compare_bound model W (powerRun (74+2*k)).power
    (64*GeneralPaperPrecisionParameterPrice.error lambda (GeneralPaperTrajectoryParameters.prepare lambda k).rows
      (GeneralPaperSourceParameters.prepare k).meshDenominator*(powerRun (32+k)).power)
  have hw := write_bound model W (GeneralPaperPrecisionParameterPrice.target lambda (GeneralPaperTrajectoryParameters.prepare lambda k).rows
    (GeneralPaperSourceParameters.prepare k).meshDenominator (powerRun (32+k)).power (powerRun (74+2*k)).power)
  have hFields := price_fields_bound W (charges model m lambda k Qv)
  have hBound := raw_bound model m lambda k Qv
  have hWord := Nat.add_le_add_left (binaryWordWidth_mono hBound) 1
  change natBits (rawCost model m lambda k Qv)≤natBits (68*model.rat (GeneralPaperSourcePreparationSizes.width m lambda k Qv)) at hWord
  have hSum : rawCost model m lambda k Qv=cost model (ops m lambda k Qv)+
      GeneralPaperSourceParameterPrice.inverseCost model.rat (powerRun (11+k)).power+
      GeneralPaperSourceParameterPrice.inverseCost model.rat (powerRun (25+k)).power+
      GeneralPaperSourceParameterPrice.inverseCost model.rat (powerRun (32+k)).power+
      GeneralPaperSourceParameterPrice.inverseCost model.rat (powerRun (29+k)).power+
      GeneralPaperIntegerWordPrice.compare model.rat (powerRun (74+2*k)).power
        (64*GeneralPaperPrecisionParameterPrice.error lambda (GeneralPaperTrajectoryParameters.prepare lambda k).rows
          (GeneralPaperSourceParameters.prepare k).meshDenominator*(powerRun (32+k)).power)+
      model.rat (natBits (GeneralPaperPrecisionParameterPrice.target lambda (GeneralPaperTrajectoryParameters.prepare lambda k).rows
        (GeneralPaperSourceParameters.prepare k).meshDenominator (powerRun (32+k)).power (powerRun (74+2*k)).power)) := by
    dsimp only [rawCost,charges,cost,ops,indices,trajectory,profit,precision]
    simp only [List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil]
    omega
  rw [(lengths model m lambda k Qv).1] at hOps
  rw [(lengths model m lambda k Qv).2] at hFields
  change priceFields W _≤67*(natBits (rawCost model m lambda k Qv)+W)+32*W at hFields
  dsimp only [rawWindow,rawProfile]
  omega

theorem native_ops (model : RationalCostModel) (W m lambda k Qv : ℕ) :
    let source := GeneralPaperSourceParameterPrice.run model.rat W k
    let t := GeneralPaperTrajectoryParameterPrice.fromCache model.rat W lambda k source.1.1
    let f := GeneralPaperDyadicPowerBits.run model.rat W (35+k)
    let e := GeneralPaperPowerCeilingBits.run model.rat W ((lambda+2)*f.1.power)
    let l := GeneralPaperPowerCeilingBits.run model.rat W m
    indices k++trajectory lambda k source.1.1.zDen.power f.1.power e.1.power e.1.doublings source.1.1.zDen.doublings++
      profit Qv t.1.rows source.1.2.meshDenominator l.1.doublings source.1.1.etaDen.power++
      precision lambda k t.1.rows source.1.2.meshDenominator source.1.1.nuDen.power=ops m lambda k Qv := by
  dsimp only
  rw [GeneralPaperSourceParameterPrice.data,GeneralPaperDyadicPowerBits.data,GeneralPaperPowerCeilingBits.data,
    GeneralPaperPowerCeilingBits.data,GeneralPaperTrajectoryParameterPrice.data model.rat W lambda k _ rfl]
  rfl

theorem native_exponents (k : ℕ) : ∀ e∈[11+k,25+k,32+k,29+k,34+k,35+k,74+2*k],e≤74+2*k := by
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

def targets (m lambda k Qv : ℕ) : List ℕ :=
  let s := GeneralPaperSourceParameters.prepare k
  let t := GeneralPaperTrajectoryParameters.prepare lambda k
  [m,GeneralPaperTrajectoryParameterPrice.target lambda k,GeneralPaperProfitParameterPrice.widthTarget m k,
    4*(2*t.rows*Qv*s.meshDenominator),
    GeneralPaperPrecisionParameterPrice.target lambda t.rows s.meshDenominator (powerRun (32+k)).power (powerRun (74+2*k)).power,
    GeneralPaperPrecisionParameterPrice.level t.rows s.meshDenominator+1]

theorem native_targets (m lambda k Qv : ℕ) :
    ∀ target∈targets m lambda k Qv,GeneralPaperSourcePreparationControls.IsTarget m lambda k Qv target := by
  intro target ht
  simp only [targets,List.mem_cons,List.not_mem_nil,or_false] at ht
  exact ht

def childPrices (model : RationalCostModel) (W m lambda k Qv : ℕ) : List ℕ :=
  ([11+k,25+k,32+k,29+k,34+k,35+k,74+2*k].map (fun e => (GeneralPaperDyadicPowerBits.run model.rat W e).2))++
    ((targets m lambda k Qv).map (fun target => (GeneralPaperPowerCeilingBits.run model.rat W target).2))

theorem native_work_data (model : RationalCostModel) (W m lambda k Qv : ℕ) :
    (GeneralPaperSourcePreparationCache.prepare model.rat W m lambda k Qv).2=
      (childPrices model W m lambda k Qv).sum+rawCost model m lambda k Qv+640*W := by
  dsimp only [GeneralPaperSourcePreparationCache.prepare]
  rw [GeneralPaperSourceParameterPrice.data,
    GeneralPaperTrajectoryParameterPrice.data model.rat W lambda k (GeneralPaperSourceParameterPrice.specification k) rfl]
  dsimp only [GeneralPaperSourceParameterPrice.run,GeneralPaperTrajectoryParameterPrice.fromCache,
    GeneralPaperProfitParameterPrice.fromCache,GeneralPaperPrecisionParameterPrice.fromCache]
  simp only [GeneralPaperDyadicPowerBits.data,GeneralPaperPowerCeilingBits.data]
  rw [cost_data]
  dsimp only [childPrices,targets,GeneralPaperSourceParameterPrice.specification]
  simp only [List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil]
  dsimp only [GeneralPaperTrajectoryParameterPrice.target,GeneralPaperProfitParameterPrice.widthTarget,
    GeneralPaperPrecisionParameterPrice.target]
  omega

def price (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  262144*GeneralPaperSourcePreparationSizes.measure m lambda k Qv*
    (W+model.rat (GeneralPaperSourcePreparationSizes.width m lambda k Qv))

def metadataCap (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  m+lambda+k+Qv+price model W m lambda k Qv+160*W+1

def sourcePrices (model : RationalCostModel) (W k : ℕ) : List ℕ :=
  [ (GeneralPaperDyadicPowerBits.run model.rat W (11+k)).2,(GeneralPaperDyadicPowerBits.run model.rat W (25+k)).2,
    (GeneralPaperDyadicPowerBits.run model.rat W (32+k)).2,(GeneralPaperDyadicPowerBits.run model.rat W (29+k)).2,
    (GeneralPaperDyadicPowerBits.run model.rat W (34+k)).2,GeneralPaperSourceParameterPrice.indexCost model.rat k,
    GeneralPaperSourceParameterPrice.inverseCost model.rat (powerRun (11+k)).power,
    GeneralPaperSourceParameterPrice.inverseCost model.rat (powerRun (25+k)).power,
    GeneralPaperSourceParameterPrice.inverseCost model.rat (powerRun (32+k)).power,
    GeneralPaperSourceParameterPrice.inverseCost model.rat (powerRun (29+k)).power]

def trajectoryPrices (model : RationalCostModel) (W lambda k : ℕ) : List ℕ :=
  let e := GeneralPaperPowerCeiling.ceiling (GeneralPaperTrajectoryParameterPrice.target lambda k)
  [(GeneralPaperDyadicPowerBits.run model.rat W (35+k)).2,
    (GeneralPaperPowerCeilingBits.run model.rat W (GeneralPaperTrajectoryParameterPrice.target lambda k)).2,
    GeneralPaperTrajectoryParameterPrice.rawWork model.rat lambda k (powerRun (11+k)).power (powerRun (35+k)).power e.power e.doublings (powerRun (11+k)).doublings]

def profitPrices (model : RationalCostModel) (W m lambda k Qv : ℕ) : List ℕ :=
  let rows := (GeneralPaperTrajectoryParameters.prepare lambda k).rows
  let mesh := (GeneralPaperSourceParameters.prepare k).meshDenominator
  [(GeneralPaperPowerCeilingBits.run model.rat W m).2,
    (GeneralPaperPowerCeilingBits.run model.rat W (GeneralPaperProfitParameterPrice.widthTarget m k)).2,
    (GeneralPaperPowerCeilingBits.run model.rat W (4*(2*rows*Qv*mesh))).2,
    GeneralPaperProfitParameterPrice.rawWork model.rat Qv rows mesh (GeneralPaperPowerCeiling.ceiling m).doublings (powerRun (25+k)).power]

def precisionPrices (model : RationalCostModel) (W lambda k : ℕ) : List ℕ :=
  let rows := (GeneralPaperTrajectoryParameters.prepare lambda k).rows
  let mesh := (GeneralPaperSourceParameters.prepare k).meshDenominator
  let nu := (powerRun (32+k)).power
  let minimum := (powerRun (74+2*k)).power
  [(GeneralPaperDyadicPowerBits.run model.rat W (74+2*k)).2,
    (GeneralPaperPowerCeilingBits.run model.rat W (GeneralPaperPrecisionParameterPrice.target lambda rows mesh nu minimum)).2,
    (GeneralPaperPowerCeilingBits.run model.rat W (GeneralPaperPrecisionParameterPrice.level rows mesh+1)).2,
    GeneralPaperPrecisionParameterPrice.rawWork model.rat lambda k rows mesh nu minimum]

def cachePrices (model : RationalCostModel) (W m lambda k Qv : ℕ) : List ℕ :=
  let source := GeneralPaperSourceParameterPrice.run model.rat W k
  let t := GeneralPaperTrajectoryParameterPrice.fromCache model.rat W lambda k source.1.1
  [source.2,t.2,(GeneralPaperProfitParameterPrice.fromCache model.rat W m Qv source.1.1 source.1.2 t.1).2,
    (GeneralPaperPrecisionParameterPrice.fromCache model.rat W lambda k source.1.1 source.1.2 t.1).2]

theorem family_data (model : RationalCostModel) (W m lambda k Qv : ℕ) :
    (sourcePrices model W k).sum+(trajectoryPrices model W lambda k).sum+(profitPrices model W m lambda k Qv).sum+
      (precisionPrices model W lambda k).sum=(childPrices model W m lambda k Qv).sum+rawCost model m lambda k Qv := by
  rw [cost_data]
  dsimp only [sourcePrices,trajectoryPrices,profitPrices,precisionPrices,childPrices,targets]
  simp only [List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil]
  omega

theorem cache_price_data (model : RationalCostModel) (W m lambda k Qv : ℕ) :
    (cachePrices model W m lambda k Qv).sum+96*W=(GeneralPaperSourcePreparationCache.prepare model.rat W m lambda k Qv).2 := by
  dsimp only [cachePrices,GeneralPaperSourcePreparationCache.prepare,List.sum_cons,List.sum_nil]
  omega

theorem family_bounds (model : RationalCostModel) (W m lambda k Qv : ℕ) :
    (sourcePrices model W k).sum≤price model W m lambda k Qv ∧
    (trajectoryPrices model W lambda k).sum≤price model W m lambda k Qv ∧
    (profitPrices model W m lambda k Qv).sum≤price model W m lambda k Qv ∧
    (precisionPrices model W lambda k).sum≤price model W m lambda k Qv ∧
    (cachePrices model W m lambda k Qv).sum≤price model W m lambda k Qv := by
  have h := native_work_data model W m lambda k Qv
  have hs := family_data model W m lambda k Qv
  have hc := cache_price_data model W m lambda k Qv
  have hw := GeneralPaperSourcePreparationEnvelope.work model.rat model.monotone W m lambda k Qv
  change _≤price model W m lambda k Qv at hw
  exact ⟨by omega,by omega,by omega,by omega,by omega⟩

def nestedWindow (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  priceFields W (sourcePrices model W k)+priceFields W (trajectoryPrices model W lambda k)+
    priceFields W (profitPrices model W m lambda k Qv)+priceFields W (precisionPrices model W lambda k)+
    priceFields W (cachePrices model W m lambda k Qv)

def nestedProfile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  55*(natBits (price model W m lambda k Qv)+W)+160*W

theorem nested_bound (model : RationalCostModel) (W m lambda k Qv : ℕ) :
    nestedWindow model W m lambda k Qv≤nestedProfile model W m lambda k Qv := by
  have hb := family_bounds model W m lambda k Qv
  have bound (xs : List ℕ) (hs : xs.sum≤price model W m lambda k Qv) :
      priceFields W xs≤(2*xs.length+1)*(natBits (price model W m lambda k Qv)+W)+32*W := by
    have h := price_fields_bound W xs
    have hWord := Nat.add_le_add_left (binaryWordWidth_mono hs) 1
    change natBits xs.sum≤natBits (price model W m lambda k Qv) at hWord
    exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right hWord W)) _)
  have a := bound _ hb.1
  have b := bound _ hb.2.1
  have c := bound _ hb.2.2.1
  have d := bound _ hb.2.2.2.1
  have e := bound _ hb.2.2.2.2
  change priceFields W (sourcePrices model W k)≤21*(natBits (price model W m lambda k Qv)+W)+32*W at a
  change priceFields W (trajectoryPrices model W lambda k)≤7*(natBits (price model W m lambda k Qv)+W)+32*W at b
  change priceFields W (profitPrices model W m lambda k Qv)≤9*(natBits (price model W m lambda k Qv)+W)+32*W at c
  change priceFields W (precisionPrices model W lambda k)≤9*(natBits (price model W m lambda k Qv)+W)+32*W at d
  change priceFields W (cachePrices model W m lambda k Qv)≤9*(natBits (price model W m lambda k Qv)+W)+32*W at e
  dsimp only [nestedWindow,nestedProfile]
  omega

def annotationFamilies (m lambda k Qv : ℕ) : List (List ℕ) :=
  let s := GeneralPaperSourceParameters.prepare k
  let t := GeneralPaperTrajectoryParameters.prepare lambda k
  let rows := t.rows
  let mesh := s.meshDenominator
  let nu := (powerRun (32+k)).power
  let minimum := (powerRun (74+2*k)).power
  [[(powerRun (11+k)).work,(powerRun (25+k)).work,(powerRun (32+k)).work,
      (powerRun (29+k)).work,(powerRun (34+k)).work,64],
    [(powerRun (11+k)).work,(powerRun (35+k)).work,
      (GeneralPaperPowerCeiling.ceiling (GeneralPaperTrajectoryParameterPrice.target lambda k)).work,24],
    [s.work,t.work,(GeneralPaperPowerCeiling.ceiling m).work,(powerRun (25+k)).work,
      (GeneralPaperPowerCeiling.ceiling (GeneralPaperProfitParameterPrice.widthTarget m k)).work,
      (GeneralPaperPowerCeiling.ceiling (4*(2*rows*Qv*mesh))).work,64],
    [(powerRun (32+k)).work,(powerRun (74+2*k)).work,
      (GeneralPaperPowerCeiling.ceiling (GeneralPaperPrecisionParameterPrice.target lambda rows mesh nu minimum)).work,
      (GeneralPaperPowerCeiling.ceiling (GeneralPaperPrecisionParameterPrice.level rows mesh+1)).work,s.work,t.work,64]]

theorem annotation_data (m lambda k Qv : ℕ) :
    (annotationFamilies m lambda k Qv).map List.sum=
      [(GeneralPaperSourceParameters.prepare k).work,(GeneralPaperTrajectoryParameters.prepare lambda k).work,
        (GeneralPaperProfitParameters.parameters m lambda k Qv).parameterWork,(GeneralPaperPowerPrecision.prepare lambda k).work] := by
  dsimp only [annotationFamilies,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    GeneralPaperSourceParameters.prepare,GeneralPaperTrajectoryParameters.prepare,
    GeneralPaperProfitParameters.parameters,GeneralPaperPowerPrecision.prepare,
    GeneralPaperTrajectoryParameterPrice.target,GeneralPaperProfitParameterPrice.widthTarget,
    GeneralPaperPrecisionParameterPrice.target,GeneralPaperPrecisionParameterPrice.level,
    GeneralPaperPrecisionParameterPrice.error]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.add_assoc]

def annotationWindow (W m lambda k Qv : ℕ) : ℕ :=
  ((annotationFamilies m lambda k Qv).map (priceFields W)).sum

def annotationProfile (W m lambda k Qv : ℕ) : ℕ :=
  52*(natBits (16384*GeneralPaperSourcePreparationSizes.measure m lambda k Qv)+W)+128*W

theorem annotation_bound (W m lambda k Qv : ℕ) :
    annotationWindow W m lambda k Qv≤annotationProfile W m lambda k Qv := by
  have hm := GeneralPaperSourcePreparationControls.metadata m lambda k Qv
  have allBound : ∀ xs∈annotationFamilies m lambda k Qv,
      xs.sum≤16384*GeneralPaperSourcePreparationSizes.measure m lambda k Qv := by
    intro xs hx
    have hx' : xs.sum∈(annotationFamilies m lambda k Qv).map List.sum := List.mem_map.mpr ⟨xs,hx,rfl⟩
    rw [annotation_data] at hx'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx'
    rcases hx' with hx'|hx'|hx'|hx'
    · rw [hx'];have h:=hm.sourceWork;omega
    · rw [hx'];have h:=hm.trajectoryWork;omega
    · rw [hx'];have h:=hm.profitWork;omega
    · rw [hx'];have h:=hm.precisionWork;omega
  have bound (xs : List ℕ) (hx : xs∈annotationFamilies m lambda k Qv) :
      priceFields W xs≤(2*xs.length+1)*(natBits (16384*GeneralPaperSourcePreparationSizes.measure m lambda k Qv)+W)+32*W := by
    have h := price_fields_bound W xs
    have hw := Nat.add_le_add_left (binaryWordWidth_mono (allBound xs hx)) 1
    exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right hw W)) _)
  let s := GeneralPaperSourceParameters.prepare k
  let t := GeneralPaperTrajectoryParameters.prepare lambda k
  let rows := t.rows
  let mesh := s.meshDenominator
  let nu := (powerRun (32+k)).power
  let minimum := (powerRun (74+2*k)).power
  have h0 := bound [(powerRun (11+k)).work,(powerRun (25+k)).work,(powerRun (32+k)).work,
      (powerRun (29+k)).work,(powerRun (34+k)).work,64] (by
    simp only [annotationFamilies,List.mem_cons,List.not_mem_nil,or_false]
    exact Or.inl True.intro)
  have h1 := bound [(powerRun (11+k)).work,(powerRun (35+k)).work,
      (GeneralPaperPowerCeiling.ceiling (GeneralPaperTrajectoryParameterPrice.target lambda k)).work,24] (by
    simp only [annotationFamilies,List.mem_cons,List.not_mem_nil,or_false]
    exact Or.inr (Or.inl True.intro))
  have h2 := bound [s.work,t.work,(GeneralPaperPowerCeiling.ceiling m).work,(powerRun (25+k)).work,
      (GeneralPaperPowerCeiling.ceiling (GeneralPaperProfitParameterPrice.widthTarget m k)).work,
      (GeneralPaperPowerCeiling.ceiling (4*(2*rows*Qv*mesh))).work,64] (by
    simp only [annotationFamilies,List.mem_cons,List.not_mem_nil,or_false]
    exact Or.inr (Or.inr (Or.inl rfl)))
  have h3 := bound [(powerRun (32+k)).work,(powerRun (74+2*k)).work,
      (GeneralPaperPowerCeiling.ceiling (GeneralPaperPrecisionParameterPrice.target lambda rows mesh nu minimum)).work,
      (GeneralPaperPowerCeiling.ceiling (GeneralPaperPrecisionParameterPrice.level rows mesh+1)).work,s.work,t.work,64] (by
    simp only [annotationFamilies,List.mem_cons,List.not_mem_nil,or_false]
    exact Or.inr (Or.inr (Or.inr rfl)))
  change priceFields W _≤13*(natBits (16384*GeneralPaperSourcePreparationSizes.measure m lambda k Qv)+W)+32*W at h0
  change priceFields W _≤9*(natBits (16384*GeneralPaperSourcePreparationSizes.measure m lambda k Qv)+W)+32*W at h1
  change priceFields W _≤15*(natBits (16384*GeneralPaperSourcePreparationSizes.measure m lambda k Qv)+W)+32*W at h2 h3
  dsimp only [s,t,rows,mesh,nu,minimum] at h0 h1 h2 h3
  dsimp only [annotationWindow,annotationFamilies,annotationProfile]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

def window (model : RationalCostModel) (W m lambda k Qv exponent target : ℕ) : ℕ :=
  let source := GeneralPaperSourceParameterPrice.run model.rat W k
  let t := GeneralPaperTrajectoryParameterPrice.fromCache model.rat W lambda k source.1.1
  let p := GeneralPaperProfitParameterPrice.fromCache model.rat W m Qv source.1.1 source.1.2 t.1
  let f := GeneralPaperPrecisionParameterPrice.fromCache model.rat W lambda k source.1.1 source.1.2 t.1
  let result := GeneralPaperSourcePreparationCache.prepare model.rat W m lambda k Qv
  GeneralPaperPreparationCacheStorage.footprint W result.1+GeneralPaperParameterTemporaryStorage.footprint W m lambda k Qv+
    rawWindow model W m lambda k Qv+nestedWindow model W m lambda k Qv+annotationWindow W m lambda k Qv+
    max (GeneralPaperDyadicConstructionStorage.window model W exponent) (GeneralPaperCeilingConstructionStorage.window model W target)+
    fields W [m,lambda,k,Qv,W,source.2,t.2,p.2,f.2,result.2,source.2+t.2,source.2+t.2+p.2,
      source.2+t.2+p.2+f.2,96*W,128*W,160*W,64*W,32*W]+256*W

def profile (model : RationalCostModel) (W m lambda k Qv : ℕ) : ℕ :=
  GeneralPaperPreparationCacheStorage.profile W m lambda k Qv+GeneralPaperParameterTemporaryStorage.profile W m lambda k Qv+
    rawProfile model W m lambda k Qv+nestedProfile model W m lambda k Qv+annotationProfile W m lambda k Qv+
    max (GeneralPaperPreparationResidentStorage.dyadicProfile model W m lambda k Qv)
      (GeneralPaperPreparationResidentStorage.ceilingProfile model W m lambda k Qv)+
    18*(natBits (metadataCap model W m lambda k Qv)+W)+288*W

theorem bounded (model : RationalCostModel) (W m lambda k Qv exponent target : ℕ)
    (he : exponent≤74+2*k) (ht : GeneralPaperSourcePreparationControls.IsTarget m lambda k Qv target) :
    window model W m lambda k Qv exponent target≤profile model W m lambda k Qv ∧
      (GeneralPaperSourcePreparationCache.prepare model.rat W m lambda k Qv).2≤price model W m lambda k Qv := by
  let source := GeneralPaperSourceParameterPrice.run model.rat W k
  let t := GeneralPaperTrajectoryParameterPrice.fromCache model.rat W lambda k source.1.1
  let p := GeneralPaperProfitParameterPrice.fromCache model.rat W m Qv source.1.1 source.1.2 t.1
  let f := GeneralPaperPrecisionParameterPrice.fromCache model.rat W lambda k source.1.1 source.1.2 t.1
  let result := GeneralPaperSourcePreparationCache.prepare model.rat W m lambda k Qv
  have hCache := GeneralPaperPreparationCacheStorage.returned model.rat W m lambda k Qv
  have hTemps := GeneralPaperParameterTemporaryStorage.bounded W m lambda k Qv
  have hRaw := raw_window_bound model W m lambda k Qv
  have hNested := nested_bound model W m lambda k Qv
  have hAnnotation := annotation_bound W m lambda k Qv
  have hDyadic := GeneralPaperDyadicConstructionStorage.whole model W m lambda k Qv exponent he
  have hD : GeneralPaperDyadicConstructionStorage.window model W exponent≤
      GeneralPaperPreparationResidentStorage.dyadicProfile model W m lambda k Qv := by
    apply hDyadic.trans
    unfold GeneralPaperPreparationResidentStorage.dyadicProfile
    exact Nat.add_le_add (Nat.mul_le_mul_right _ (by omega : exponent+1≤74+2*k+1))
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 64 (by omega : exponent+1≤74+2*k+1)))
  have hC := GeneralPaperCeilingConstructionStorage.source model W m lambda k Qv target ht
  change GeneralPaperCeilingConstructionStorage.window model W target≤
    GeneralPaperPreparationResidentStorage.ceilingProfile model W m lambda k Qv at hC
  have hChild := max_le_max hD hC
  have hWork := GeneralPaperSourcePreparationEnvelope.work model.rat model.monotone W m lambda k Qv
  change result.2≤price model W m lambda k Qv at hWork
  have hWorkEq : result.2=source.2+t.2+p.2+f.2+96*W := rfl
  have hf := fields_bound W (natBits (metadataCap model W m lambda k Qv))
    [m,lambda,k,Qv,W,source.2,t.2,p.2,f.2,result.2,source.2+t.2,source.2+t.2+p.2,
      source.2+t.2+p.2+f.2,96*W,128*W,160*W,64*W,32*W] (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals unfold metadataCap;omega)
  change fields W _≤18*(natBits (metadataCap model W m lambda k Qv)+W)+32*W at hf
  refine ⟨?_,hWork⟩
  have hCore := Nat.add_le_add_right (Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hCache hTemps) hRaw) hNested) hAnnotation) hChild) hf) (256*W)
  exact hCore.trans_eq (by dsimp only [profile];ring)

theorem returned (model : RationalCostModel) (W m lambda k Qv exponent target : ℕ) :
    GeneralPaperPreparationCacheStorage.footprint W (GeneralPaperSourcePreparationCache.prepare model.rat W m lambda k Qv).1≤
      window model W m lambda k Qv exponent target := by
  dsimp only [window]
  omega

end Blotto.GeneralPaperSourceControlsConstructionStorage
