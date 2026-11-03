import Blotto.GeneralPaperNativeUnequalBudgetContract

/-! Stored whole-row and shift support counts have the paper sizes with
no original-precision/accuracy-encoding logarithm. Native controls, not an
enumerated support, supply the two powers of two. -/
namespace Blotto.GeneralPaperNativeSupportCardinality
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters GeneralPaperNativeResourceReferenceGrowth
open GeneralPaperNativeWorkingSpaceHeadline (epsilon epsilon_positive exponent_exact)
open GeneralPaperNativeDrawHeadline GeneralPaperNativeUnequalBudgetContract
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 16384

theorem source_rows_core : ∃ A e : ℕ,∀ x : GeneralPaperSourceWordGrowth.Input,
    (GeneralPaperTrajectoryParameters.prepare (GeneralPaperSourceWordGrowth.alphabet x).lambda x.k).rows≤
      A*GeneralPaperSourceRateAlgebra.monomial 1 0 3 x*(GeneralPaperSourceCoreLogBound.coreLog x)^e :=
  GeneralPaperSourceCoreLogBound.remove_unused_height GeneralPaperSourceStaticConstructionRates.sharp_rows
    (fun _ => rfl) (fun _ => rfl)

theorem rows_headline (model : RationalCostModel) : ∃ A e : ℕ,∀ p : Problem,epsilon p<1 →
    (rows model p:ℚ)≤(A:ℚ)*(GeneralPaperRealHeadlineParameters.nStar p.n (epsilon p)/(epsilon p)^3)*
      (GeneralPaperRealHeadlineParameters.logarithm p.n (epsilon p):ℚ)^e := by
  obtain ⟨A,e,hA⟩ := source_rows_core
  refine ⟨A*296*4^e,e,?_⟩
  intro p hOne
  have hE := epsilon_positive p
  let N := GeneralPaperRealHeadlineParameters.nStar p.n (epsilon p)
  let L := GeneralPaperRealHeadlineParameters.logarithm p.n (epsilon p)
  have hStar : 1≤N := GeneralPaperRealHeadlineParameters.nstar_positive p.n p.selector.fields_positive (epsilon p) (epsilon_positive p) hOne
  have hM : ((reduced model p).m:ℚ)≤36*N := by
    have h := GeneralPaperOriginalSourceValueContract.dyadic_field_count false model 1 (epsilon p) (epsilon_positive p) hOne p.values p.selector p.correct
    rw [←exponent_exact p] at h
    exact h
  have hPower : (2:ℚ)^(exponent p)≤2/epsilon p := by
    rw [exponent_exact p]
    exact GeneralPaperRealHeadlineParameters.power_bound (epsilon p) (epsilon_positive p) hOne
  have hM' : ((reduced model p).m:ℚ)+1≤37*N := by linarith only [hM,hStar]
  have hP3 : ((2:ℚ)^(exponent p))^3≤(2/epsilon p)^3 := by gcongr
  have hProduct := mul_le_mul hM' hP3 (by positivity) (by positivity)
  have hScale : (((reduced model p).m:ℚ)+1)*((2:ℚ)^(exponent p))^3≤296*(N/(epsilon p)^3) :=
    hProduct.trans_eq (by ring)
  have hCore := (GeneralPaperOriginalSourceValueContract.original_log_bound false model 1 (exponent p) (ledger p)
    p.values p.selector p.correct p.budget p.budget_valid (source model p).hB).2
  change GeneralPaperSourceCoreLogBound.coreLog (source model p)≤4*GeneralPaperOriginalSourceValueContract.inputLog p.n (exponent p) 0 at hCore
  have hInput : GeneralPaperOriginalSourceValueContract.inputLog p.n (exponent p) 0≤L := by
    rw [exponent_exact p]
    exact GeneralPaperRealHeadlineParameters.log_bound p.n (epsilon p)
  have hLog := hCore.trans (Nat.mul_le_mul_left 4 hInput)
  have hNative := (hA (source model p)).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hLog e))
  have hNatRate : GeneralPaperSourceRateAlgebra.monomial 1 0 3 (source model p)=((reduced model p).m+1)*(2^(exponent p))^3 := by
    simp only [GeneralPaperSourceRateAlgebra.monomial,pow_one,pow_zero,Nat.mul_one,
      GeneralPaperNativeSourceRates.fields,GeneralPaperNativeSourceRates.accuracy,source_count,source_exponent,prepared,reduced]
  rw [hNatRate] at hNative
  have hQ : (rows model p:ℚ)≤(A:ℚ)*((((reduced model p).m:ℚ)+1)*((2:ℚ)^(exponent p))^3)*((4:ℚ)*(L:ℚ))^e := by
    exact_mod_cast hNative
  calc
    _≤(A:ℚ)*((((reduced model p).m:ℚ)+1)*((2:ℚ)^(exponent p))^3)*((4:ℚ)*(L:ℚ))^e := hQ
    _≤(A:ℚ)*(296*(N/(epsilon p)^3))*((4:ℚ)*(L:ℚ))^e := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hScale (by positivity)) (by positivity)
    _= _ := by dsimp only [N,L];push_cast;rw [mul_pow];ring

theorem closed_shifts {n : ℕ} (Ap : ℕ) (raw : GeneralPaperAccuracyStrategyDriver.Prepared n)
    (sampler : GeneralPaperStoredStrategySampler.Sampler n (GeneralPaperClosedSamplerConstructionStorage.rows raw) (GeneralPaperClosedSamplerConstructionStorage.labels raw))
    (hSampler : (GeneralPaperClosedStrategyDriver.close (fun w => w) Ap raw).1=some sampler) :
    sampler.controls.shifts=GeneralPaperNativeSelectedSecurity.count raw.exponent := by
  cases he:raw.strategies.description with
  | none => simp only [GeneralPaperClosedStrategyDriver.close,he] at hSampler;cases hSampler
  | some description =>
    have hData := GeneralPaperClosedStrategyDriver.close_some (fun w => w) Ap raw description he
    have hEq := Option.some.inj (hSampler.symm.trans hData)
    rw [hEq]
    rfl

theorem controls_counts (model : RationalCostModel) (C d : ℕ) (p : Problem) (sampler : SamplerFor model C d p)
    (hSampler : (returned model C d p).sampler=some sampler) :
    sampler.controls.rows=rows model p ∧ sampler.controls.shifts=GeneralPaperNativeSelectedSecurity.count (exponent p) := by
  have hType : (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet (returned model C d p).raw.strategies.original.reduced.m
      (returned model C d p).raw.exponent).lambda (returned model C d p).raw.exponent).rows=rows model p := by
    rw [returned_reduced,returned_exponent]
    rfl
  have hRows := sampler.controls.rows_eq.trans hType
  have hShifts : sampler.controls.shifts=GeneralPaperNativeSelectedSecurity.count (returned model C d p).raw.exponent := by
    apply closed_shifts (word model C d p) (returned model C d p).raw sampler
    exact hSampler
  exact ⟨hRows,hShifts.trans (congrArg GeneralPaperNativeSelectedSecurity.count (returned_exponent model C d p))⟩

theorem shifts_headline (p : Problem) (hOne : epsilon p<1) :
    (GeneralPaperNativeSelectedSecurity.count (exponent p):ℚ)≤128/epsilon p := by
  have hPower : (2:ℚ)^(exponent p)≤2/epsilon p := by
    rw [exponent_exact p]
    exact GeneralPaperRealHeadlineParameters.power_bound (epsilon p) (epsilon_positive p) hOne
  have hEq : (GeneralPaperNativeSelectedSecurity.count (exponent p):ℚ)=64*(2:ℚ)^(exponent p) := by
    rw [GeneralPaperNativeSelectedSecurity.count_power]
    push_cast
    rw [pow_add]
    norm_num
    ring
  rw [hEq]
  calc
    _≤64*(2/epsilon p) := mul_le_mul_of_nonneg_left hPower (by norm_num)
    _= _ := by ring


def Support (model : RationalCostModel) (C d A e : ℕ) (p : Problem) : Prop :=
  ∀ sampler : SamplerFor model C d p,(returned model C d p).sampler=some sampler →
    (sampler.controls.rows:ℚ)≤(A:ℚ)*(GeneralPaperRealHeadlineParameters.nStar p.n (epsilon p)/(epsilon p)^3)*
      (GeneralPaperRealHeadlineParameters.logarithm p.n (epsilon p):ℚ)^e ∧
    (sampler.controls.shifts:ℚ)≤128/epsilon p ∧
    (∃ R : ℕ,sampler.controls.rows=2^R) ∧ (∃ L : ℕ,sampler.controls.shifts=2^L)

theorem uniform_support (model : RationalCostModel) (C d : ℕ) : ∃ A e : ℕ,∀ p : Problem,epsilon p<1 → Support model C d A e p := by
  obtain ⟨A,e,hA⟩ := rows_headline model
  refine ⟨A,e,?_⟩
  intro p hOne sampler hSampler
  have hCounts := controls_counts model C d p sampler hSampler
  refine ⟨?_,?_,⟨sampler.controls.rowBits,sampler.controls.rows_power⟩,⟨sampler.controls.shiftBits,sampler.controls.shifts_power⟩⟩
  · rw [hCounts.1]
    exact hA p hOne
  · rw [hCounts.2]
    exact shifts_headline p hOne

theorem uniform_pair_selection (model : RationalCostModel) (C d : ℕ) (p : Problem) (sampler : SamplerFor model C d p)
    (f : Fin sampler.controls.rows → Fin sampler.controls.shifts → Allocation p.n) :
    (fairBitLaw (sampler.controls.rowBits+sampler.controls.shiftBits)).map (fun bits =>
      let selected := GeneralPaperNativeDyadicBlocks.run model.rat (drawReference model C d p)
        sampler.controls.rowBits sampler.controls.shiftBits sampler.controls.rows sampler.controls.shifts
        sampler.controls.rows_power sampler.controls.shifts_power (FixedArrayTable.ofFn bits)
      f selected.row selected.shift)=
      GeneralPaperUniformRowLaw.mixture (sampler.controls.rows_power ▸ Nat.two_pow_pos sampler.controls.rowBits) (fun i =>
        GeneralPaperUniformRowLaw.law (sampler.controls.shifts_power ▸ Nat.two_pow_pos sampler.controls.shiftBits) (f i)) :=
  GeneralPaperFairRowShiftLaw.native model.rat (drawReference model C d p) _ _ _ _ sampler.controls.rows_power sampler.controls.shifts_power f

theorem full_bit_contract {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ At et As es Ad AT eT : ℕ,∀ p : Problem,epsilon p<1 →
      Contract model C d At et As es Ad p ∧ Support model C d AT eT p := by
  obtain ⟨At,et,As,es,Ad,hCore⟩ := uniform_contract hg
  obtain ⟨AT,eT,hSupport⟩ := uniform_support model C d
  exact ⟨At,et,As,es,Ad,AT,eT,fun p hOne => ⟨hCore p hOne,hSupport p hOne⟩⟩

theorem full_frame_contract {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ At et As es Ad AT eT : ℕ,∀ p : Problem,epsilon p<1 →
      FrameContract model C d At et As es Ad p ∧ Support model C d AT eT p := by
  obtain ⟨At,et,As,es,Ad,hCore⟩ := uniform_frame_contract hg
  obtain ⟨AT,eT,hSupport⟩ := uniform_support model C d
  exact ⟨At,et,As,es,Ad,AT,eT,fun p hOne => ⟨hCore p hOne,hSupport p hOne⟩⟩

end Blotto.GeneralPaperNativeSupportCardinality
