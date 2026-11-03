import Blotto.GeneralPaperOriginalStrategyEquilibrium
import Blotto.GeneralPaperSourceStaticConstructionRates

/-! Complete arithmetic work for the actual original-input retained
strategy producer, including source, shared circle preparation and parent
charges. Bit callers/owners and accuracy decoding remain separate joins. -/
namespace Blotto.GeneralPaperStrategyPreparationWork
open GeneralPaperStrategyDescription GeneralPaperOriginalStrategyDriver GeneralPaperOriginalDrawEquilibrium
open GeneralPaperSourceWordGrowth GeneralPaperSourceRateAlgebra GeneralPaperSourceSoftBounds
open GeneralPaperNativeSelectedSecurity
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

theorem make_arithmetic_work {n T K : ℕ} (model : RationalCostModel) (o : GeneralPaperReducedValuesDriver.Output n)
    (hRep : GeneralPaperNativeReductionShape.ReplacedShape o) (hNo : GeneralPaperUnreplacedShape.Shape o)
    (hR : 0<o.representatives) (hConserved : GeneralPaperCircleActualWeights.Conserved o) (physical : Columns T o.m K) :
    (make (fun _ => 1) (fun _ => 1) 1 o hRep hNo hR physical).2≤
      325*o.classified.light.size+529+2*GeneralPaperCachedCircleWork.rowsProfile T o.representatives 1 1 := by
  by_cases hFlag:o.replaced=true
  · obtain ⟨hm,_⟩ := hRep hFlag
    rw [make_circle (fun _ => 1) (fun _ => 1) 1 o hRep hNo hR physical hFlag hm]
    have h := GeneralPaperCachedCircleWork.pair_arithmetic model o hm hConserved physical
    dsimp only
    omega
  · have hFalse : o.replaced=false := by cases he:o.replaced <;> simp_all
    obtain ⟨hm,_⟩ := hNo hFalse
    rw [make_direct (fun _ => 1) (fun _ => 1) 1 o hRep hNo hR physical hFalse hm]
    dsimp only
    omega

def circlePrice (m k : ℕ) : ℕ := 529+2*GeneralPaperCachedCircleWork.rowsProfile
  (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet m k).lambda k).rows (8*2^k) 1 1

theorem light_size {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ) :
    (GeneralPaperOriginalValueReduction.run bits model W k values).1.classified.light.size≤n := by
  have h := Fintype.card_congr (GeneralPaperLightFieldIndexEquiv.originalEquiv bits model W k values)
  simp only [Fintype.card_fin] at h
  omega

theorem arithmetic_work {n : ℕ} (model : RationalCostModel) (k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℝ) (hb : 0<b ∧ b<1) :
    let o := (GeneralPaperOriginalValueReduction.run false model 1 k values).1
    (arithmetic model k values v hv b).2≤(GeneralPaperOriginalSourceValueDriver.arithmetic model k values v hv b).2+
      325*n+circlePrice o.m k+192 := by
  obtain ⟨physical,pair,_hSource,_hMatches,_hDescription,hWork⟩ := arithmetic_return model k values v hv b hb
  have h := make_arithmetic_work model (GeneralPaperOriginalValueReduction.run false model 1 k values).1
    (GeneralPaperNativeReductionShape.original_shape false model 1 k values)
    (GeneralPaperUnreplacedShape.original_shape false model 1 k values)
    (GeneralPaperNativeCircleLoss.original_representatives_positive false model 1 k values)
    (GeneralPaperCircleActualWeights.original_sum false model 1 k values) physical
  rw [GeneralPaperNativeReductionShape.original_representatives] at h
  have hLight := light_size false model 1 k values
  dsimp only
  rw [hWork]
  unfold circlePrice
  unfold GeneralPaperLightFieldReduction.representatives at h
  omega

theorem circle_rate : Rated (fun x => circlePrice x.m x.k) 1 0 4 := by
  have ht := GeneralPaperSourceStaticConstructionRates.sharp_rows
  have hp : Rated (fun x : Input => 2^x.k) 0 0 1 := by
    simpa only [Nat.zero_add] using dyadic_accuracy 0
  have hr : Rated (fun x : Input => 8*2^x.k) 0 0 1 := by source_space
  have hw : Rated (fun x : Input => binaryWordWidth (8*2^x.k+1)) 0 0 0 := word _ (by fun_prop)
  unfold circlePrice GeneralPaperCachedCircleWork.rowsProfile GeneralPaperCachedCircleWork.rowProfile
    GeneralPaperCachedCircleWork.representativesProfile GeneralPaperNativeSortedRows.oneProfile
    GeneralPaperNativeRepresentativeSort.profile GeneralPaperPricedSort.profile
  change Rated _ 1 0 4
  source_space

theorem circle_core_time : ∃ A e : ℕ,∀ x : Input,circlePrice x.m x.k≤A*monomial 2 0 5 x*(GeneralPaperSourceCoreLogBound.coreLog x)^e := by
  apply GeneralPaperSourceCoreLogBound.remove_unused_height (weaken circle_rate (by decide) (by decide) (by decide))
  · intro x
    rfl
  · intro x
    rfl


theorem real_input_time (model : RationalCostModel) :
    ∃ A e : ℕ,∀ {n : ℕ} (k : ℕ) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
      (hv : ∀ j,values.read j=v.weight j) (b : ℝ),0<b ∧ b<1 →
      let o := (GeneralPaperOriginalSourceValuePreparation.run false model 1 k values v hv).1
      let x := GeneralPaperOriginalSourceValuePreparation.input o k 2 (1/2) (by norm_num) (by norm_num [RationalHeight])
      (arithmetic model k values v hv b).2≤A*(n+1+monomial 2 0 5 x)*(GeneralPaperOriginalSourceValueContract.inputLog n k 0)^e := by
  obtain ⟨As,es,hSource⟩ := GeneralPaperOriginalSourceValueContract.real_input_time model
  obtain ⟨Ac,ec,hCircle⟩ := circle_core_time
  refine ⟨As+Ac*4^ec+517,es+ec+2,?_⟩
  intro n k values v hv b hb
  let o := (GeneralPaperOriginalSourceValuePreparation.run false model 1 k values v hv).1
  let x := GeneralPaperOriginalSourceValuePreparation.input o k 2 (1/2) (by norm_num) (by norm_num [RationalHeight])
  let R := n+1+monomial 2 0 5 x
  let L := GeneralPaperOriginalSourceValueContract.inputLog n k 0
  let D := es+ec+2
  have hL : 1≤L := GeneralPaperOriginalSourceValueContract.input_log_positive n k 0
  have hN : n+1≤R := by dsimp only [R];omega
  have hM : monomial 2 0 5 x≤R := by dsimp only [R];omega
  have hEs : L^es≤L^D := Nat.pow_le_pow_right hL (by dsimp only [D];omega)
  have hEc : L^ec≤L^D := Nat.pow_le_pow_right hL (by dsimp only [D];omega)
  have hLog : GeneralPaperSourceCoreLogBound.coreLog x≤4*L :=
    (GeneralPaperOriginalSourceValueContract.original_log_bound false model 1 k 2 values v hv (1/2)
      (by norm_num) (by norm_num [RationalHeight])).2
  have hS : (GeneralPaperOriginalSourceValueDriver.arithmetic model k values v hv b).2≤As*R*L^D :=
    (hSource k values v hv b hb).trans (Nat.mul_le_mul_left _ hEs)
  have hC : circlePrice (GeneralPaperOriginalValueReduction.run false model 1 k values).1.m k≤Ac*4^ec*R*L^D := by
    calc
      _≤Ac*monomial 2 0 5 x*(GeneralPaperSourceCoreLogBound.coreLog x)^ec := hCircle x
      _≤Ac*monomial 2 0 5 x*(4*L)^ec := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hLog ec)
      _=Ac*4^ec*monomial 2 0 5 x*L^ec := by rw [mul_pow];ring
      _≤Ac*4^ec*R*L^D := Nat.mul_le_mul (Nat.mul_le_mul_left _ hM) hEc
  have hRP : R≤R*L^D := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left R (Nat.one_le_pow D L hL)
  have hParent : 325*n+192≤517*R*L^D := by nlinarith only [hN,hRP]
  exact (arithmetic_work model k values v hv b hb).trans (by
    change _≤(As+Ac*4^ec+517)*R*L^D
    nlinarith only [hS,hC,hParent])


theorem real_time_and_epsilon (model : RationalCostModel) :
    ∃ A e : ℕ,∀ {n : ℕ} (k : ℕ)
    (epsilon : ℚ) (_hE : 0<epsilon) (_hOne : epsilon<1) (_hk : k=(GeneralPaperDyadicAccuracy.prepare epsilon).exponent)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (_hb : 0<b ∧ b<1) (primitive : ℕ → ℕ),
    let o := (GeneralPaperOriginalValueReduction.run false model 1 k values).1
    let trajectory := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hRows := GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let hShift := count_power k
    ∃ description : Description o trajectory.rows (GeneralPaperProxyParameters.prepare o.m k).K,
      (arithmetic model k values v hv (b:ℝ)).1.description=some description ∧
      (arithmetic model k values v hv (b:ℝ)).2≤A*(n+1+monomial 2 0 5
        (GeneralPaperOriginalSourceValuePreparation.input (GeneralPaperOriginalSourceValuePreparation.run false model 1 k values v hv).1
          k 2 (1/2) (by norm_num) (by norm_num [RationalHeight])))*(GeneralPaperOriginalSourceValueContract.inputLog n k 0)^e ∧
      let μ := law false primitive 1 trajectory.rowBits (k+6) (count k) hRows hShift model o description 1 false
      let ν := law false primitive 1 trajectory.rowBits (k+6) (count k) hRows hShift model o description b true
      Supported 1 μ ∧ Supported (b:ℝ) ν ∧ regret v.values 1 μ ν≤(epsilon:ℝ) ∧ regret v.values (b:ℝ) ν μ≤(epsilon:ℝ) ∧
      ∀ fresh : Fin (trajectory.rowBits+(k+6)) → Bool,
        Feasible 1 (fun j => ((run false primitive 1 trajectory.rowBits (k+6) (count k) hRows hShift model o description 1 false fresh).output.read j:ℝ)) ∧
        Feasible (b:ℝ) (fun j => ((run false primitive 1 trajectory.rowBits (k+6) (count k) hRows hShift model o description b true fresh).output.read j:ℝ)) := by
  obtain ⟨A,e,hTime⟩ := real_input_time model
  refine ⟨A,e,?_⟩
  intro n k epsilon hE hOne hk values v hv b hb primitive
  obtain ⟨description,hRun,hA,hB,hRich,hPoor,hFeasible⟩ :=
    GeneralPaperOriginalStrategyEquilibrium.arithmetic_pointwise model k epsilon hE hOne hk values v hv b hb primitive
  dsimp only
  exact ⟨description,hRun,hTime k values v hv (b:ℝ) (by exact_mod_cast hb),hA,hB,hRich,hPoor,hFeasible⟩

end Blotto.GeneralPaperStrategyPreparationWork
