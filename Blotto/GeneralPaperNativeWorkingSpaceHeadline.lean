import Blotto.GeneralPaperNativeWorkingPreparationRates

/-! Actual-input working-space headline in the paper's epsilon/n_* units.
Original input and Boolean accuracy lengths stay additive. This covers the
complete common-word reserve; time, drawing and boundary wrappers are
separate joins. -/
namespace Blotto.GeneralPaperNativeWorkingSpaceHeadline
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters GeneralPaperNativeResourceReferenceGrowth
open GeneralPaperNativeWorkingResourceRates GeneralPaperNativeWorkingPreparationRates
open GeneralPaperOriginalSourceDriverConstructionStorage
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

def epsilon (p : Problem) : ℚ := (p.words.numerator.value:ℚ)/p.words.denominator.value

theorem epsilon_positive (p : Problem) : 0<epsilon p :=
  div_pos (by exact_mod_cast p.words.numerator.value_pos) (by exact_mod_cast p.words.denominator.value_pos)

theorem exponent_exact (p : Problem) : exponent p=(GeneralPaperDyadicAccuracy.prepare (epsilon p)).exponent :=
  GeneralPaperBinaryAccuracy.exact_exponent (fun w => w) 1 p.words (epsilon p) rfl

def paperLog (p : Problem) : ℕ :=
  129+binaryWordWidth (p.n+4)+binaryWordWidth ⌈(epsilon p)⁻¹⌉₊+binaryWordWidth (ledger p+1)

theorem log_comparison (model : RationalCostModel) (p : Problem) : logarithm model p≤4*paperLog p := by
  have h := (GeneralPaperOriginalSourceValueContract.original_log_bound false model 1 (exponent p) (ledger p)
    p.values p.selector p.correct p.budget p.budget_valid (source model p).hB).1
  change logarithm model p≤4*GeneralPaperOriginalSourceValueContract.inputLog p.n (exponent p) (ledger p) at h
  have hk := GeneralPaperRealHeadlineParameters.exponent_bound (epsilon p)
  rw [←exponent_exact p] at hk
  have hInput : GeneralPaperOriginalSourceValueContract.inputLog p.n (exponent p) (ledger p)≤paperLog p := by
    unfold GeneralPaperOriginalSourceValueContract.inputLog paperLog
    omega
  exact h.trans (Nat.mul_le_mul_left 4 hInput)

def spaceScale (p : Problem) : ℚ :=
  ((ledger p+1:ℕ):ℚ)+(GeneralPaperRealHeadlineParameters.nStar p.n (epsilon p))^3/(epsilon p)^4

theorem structural_scale (model : RationalCostModel) (p : Problem) (hOne : epsilon p<1) :
    (rate model p:ℚ)≤810448*spaceScale p := by
  let N := GeneralPaperRealHeadlineParameters.nStar p.n (epsilon p)
  have hStar : 1≤N := GeneralPaperRealHeadlineParameters.nstar_positive p.n p.selector.fields_positive
    (epsilon p) (epsilon_positive p) hOne
  have hM : ((reduced model p).m:ℚ)≤36*N := by
    have h := GeneralPaperOriginalSourceValueContract.dyadic_field_count false model 1 (epsilon p) (epsilon_positive p) hOne
      p.values p.selector p.correct
    rw [←exponent_exact p] at h
    exact h
  have hPower : (2:ℚ)^(exponent p)≤2/epsilon p := by
    rw [exponent_exact p]
    exact GeneralPaperRealHeadlineParameters.power_bound (epsilon p) (epsilon_positive p) hOne
  have hM' : ((reduced model p).m:ℚ)+1≤37*N := by linarith only [hM,hStar]
  have hM3 : (((reduced model p).m:ℚ)+1)^3≤(37*N)^3 := by gcongr
  have hP4 : ((2:ℚ)^(exponent p))^4≤(2/epsilon p)^4 := by gcongr
  have hProduct := mul_le_mul hM3 hP4 (by positivity) (by positivity)
  have hProduct' : (((reduced model p).m:ℚ)+1)^3*((2:ℚ)^(exponent p))^4≤810448*(N^3/(epsilon p)^4) :=
    hProduct.trans_eq (by ring)
  have hBase : ((ledger p+1:ℕ):ℚ)≤810448*((ledger p+1:ℕ):ℚ) := by nlinarith only [Nat.cast_nonneg (α:=ℚ) (ledger p+1)]
  have hTotal := add_le_add hBase hProduct'
  calc
    (rate model p:ℚ)=((ledger p+1:ℕ):ℚ)+(((reduced model p).m:ℚ)+1)^3*((2:ℚ)^(exponent p))^4 := by
      simp only [rate,GeneralPaperSourceRateAlgebra.monomial,GeneralPaperNativeSourceRates.fields,
        GeneralPaperNativeSourceRates.accuracy,pow_zero,Nat.mul_one,source_count,source_exponent,prepared,reduced,
        Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    _≤810448*((ledger p+1:ℕ):ℚ)+810448*(N^3/(epsilon p)^4) := hTotal
    _=810448*spaceScale p := by unfold spaceScale;dsimp only [N];ring

theorem complete_reserve_headline {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ p : Problem,epsilon p<1 →
      (reserve model C d (word model C d p) p:ℚ)≤(A:ℚ)*spaceScale p*(paperLog p:ℚ)^e := by
  obtain ⟨A,e,hA⟩ := reserve_at_common_word_rate hg
  refine ⟨A*810448*4^e,e,?_⟩
  intro p hOne
  have hRate := structural_scale model p hOne
  have hLog := log_comparison model p
  have hNat := (hA p).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hLog e))
  have hCast : (reserve model C d (word model C d p) p:ℚ)≤
      (A:ℚ)*(rate model p:ℚ)*((4:ℚ)*(paperLog p:ℚ))^e := by exact_mod_cast hNat
  calc
    _≤(A:ℚ)*(rate model p:ℚ)*((4:ℚ)*(paperLog p:ℚ))^e := hCast
    _≤(A:ℚ)*(810448*spaceScale p)*((4:ℚ)*(paperLog p:ℚ))^e := by gcongr
    _= _ := by push_cast;rw [mul_pow];ring

theorem native_bit_window_headline {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ p : Problem,epsilon p<1 →
    let W := word model C d p
    let k := (GeneralPaperBinaryAccuracy.prepare (fun w => w) W p.words).1
    let actual := (GeneralPaperOriginalSourceValuePreparation.run true model W k p.values p.selector p.correct).1
    ∀ (cS : SourceCursor actual.reduced.m k actual.Qv)
      (cD : GeneralPaperStrategyDescriptionConstructionStorage.Cursor actual.reduced (GeneralPaperOriginalStrategyConstructionStorage.rows k actual.reduced)),
      let observed := GeneralPaperClosedStrategyConstructionStorage.window W
        (GeneralPaperAccuracyStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget p.budget_valid).1
        (GeneralPaperAccuracyStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget p.budget_valid).2
        (GeneralPaperAccuracyStrategyConstructionStorage.window model W p.words p.values p.selector p.correct p.budget p.budget_valid cS cD)
      (observed:ℚ)≤(A:ℚ)*spaceScale p*(paperLog p:ℚ)^e ∧ observed<2^W ∧
        GeneralPaperClosedDescriptionStorage.preparedFoot W
          (GeneralPaperClosedStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget p.budget_valid).1<2^W := by
  obtain ⟨A,e,hA⟩ := complete_reserve_headline hg
  refine ⟨A,e,?_⟩
  intro p hOne
  dsimp only
  intro cS cD
  have h := GeneralPaperNativeResourceWordContract.bit_contract hg p cS cD
  exact ⟨(Nat.cast_le.mpr h.1).trans (hA p hOne),h.2⟩

end Blotto.GeneralPaperNativeWorkingSpaceHeadline
