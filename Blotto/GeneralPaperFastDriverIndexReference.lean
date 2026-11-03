import Blotto.GeneralPaperFastWholeDriverStorageRates

/-! Analytic index ranges for the complete native driver. Constructor
frontiers, power/grid cursors and original input bits join all preceding
source/compiler ranges. These closed bounds never run an input or capacity
census and retain additive original-input length in the space rate. -/
namespace Blotto.GeneralPaperFastDriverIndexReference
open GeneralPaperSourceWordGrowth GeneralPaperNativeSourceRates GeneralPaperSourceRateAlgebra GeneralPaperSourceSoftBounds
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def gridCount (x : Input) : ℕ :=
  let p := GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv
  GeneralPaperProfitGridPrice.count p.width p.exponent

def core (x : Input) : ℕ :=
  GeneralPaperCompilerReference.indexSize x.m x.k+
    1024*(GeneralPaperSourcePreparationSizes.measure x.m (alphabet x).lambda x.k x.Qv+1)+
    16*(gridCount x+1)+16*(GeneralPaperPrecallControlWord.measure x.m x.k+1)+8*(alphabet x).lambda+
    GeneralPaperControlMaterializationStorage.powerWord x.m (alphabet x).lambda x.k x.Qv+
    GeneralPaperControlMaterializationStorage.gridWord x.m (alphabet x).lambda x.k x.Qv+1

def size (x : Input) : ℕ := x.B+core x

theorem previous_le (x : Input) : GeneralPaperCompilerReference.indexSize x.m x.k≤size x := by unfold size core;omega

theorem front_measure_rate : Rated (fun x => GeneralPaperPrecallControlWord.measure x.m x.k) 1 0 1 := by
  have hL := GeneralPaperSourceSharpOperandRates.alphabet_length
  apply GeneralPaperSourceSoftBounds.dominated (g:=fun x => x.k+8*(alphabet x).lambda+64)
  · change Rated (fun x => x.k+8*(alphabet x).lambda+64) 1 0 1
    source_space
  · intro x
    exact GeneralPaperPrecallWordEnvelope.measure_bound x.m x.k

def coreCertificate (W : Input → ℕ) (hW : Tight W) : Certificate (fun x => core x*W x) := by
  have hOld : Rated (fun x => GeneralPaperCompilerReference.indexSize x.m x.k) 1 0 3 := by
    have h := (GeneralPaperCachedBitPairReferenceContract.indexCertificate (fun _ => 1) (tight_constant 1)).bound
    change Rated (fun x => GeneralPaperCompilerReference.indexSize x.m x.k*1) 1 0 3 at h
    simpa only [Nat.mul_one] using h
  have hF := front_measure_rate
  have hL := GeneralPaperSourceSharpOperandRates.alphabet_length
  have hU := poly (poly_tight _ GeneralPaperFastWholeDriverStorageRates.power_word_tight)
  have hV := poly (poly_tight _ GeneralPaperFastWholeDriverStorageRates.grid_word_tight)
  have hR : Rated W 0 0 0 := poly (poly_tight W hW)
  refine ⟨_,_,_,by
    dsimp only [core,gridCount,GeneralPaperProfitGridPrice.count]
    source_space⟩

theorem core_degrees (W : Input → ℕ) (hW : Tight W) :
    ((coreCertificate W hW).fields,(coreCertificate W hW).symbols,(coreCertificate W hW).accuracy)=(1,0,3) := rfl

theorem core_small : Small core := by
  have hs : Small (fun x => core x*1) := GeneralPaperSourceRowsStorageRates.soft_small
    (coreCertificate (fun _ => 1) (tight_constant 1)).bound (by
      change Small (monomial 1 0 3)
      unfold monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
      fun_prop)
  simpa only [Nat.mul_one] using hs

theorem size_small : Small size := by
  have h := core_small
  unfold size
  fun_prop

theorem rate (W : Input → ℕ) (hW : Tight W) : Soft GeneralPaperFastFrontStorageRates.rate (fun x => size x*W x) := by
  have hB : Soft GeneralPaperFastFrontStorageRates.rate Input.B := GeneralPaperFastFrontStorageRates.input_rate
  have hInput := mul_poly hB (poly_tight W hW)
  have hCore : Soft GeneralPaperFastFrontStorageRates.rate (fun x => core x*W x) :=
    rate_mono (coreCertificate W hW).bound (fun x => by
      have h := monomial_mono (by decide : 1≤3) (by decide : 0≤0) (by decide : 3≤4) x
      change monomial 1 0 3 x≤x.B+1+monomial 3 0 4 x
      omega)
  simpa only [size,Nat.add_mul] using add_same hInput hCore

theorem construction_ranges (x : Input) :
    let M := GeneralPaperSourcePreparationSizes.measure x.m (alphabet x).lambda x.k x.Qv
    x.B≤size x ∧ 74+2*x.k+1≤size x ∧ 128*M+1≤size x ∧ gridCount x+1≤size x ∧
      GeneralPaperPrecallControlWord.measure x.m x.k+1≤size x ∧ (alphabet x).lambda≤size x ∧
      GeneralPaperControlMaterializationStorage.powerWord x.m (alphabet x).lambda x.k x.Qv≤size x ∧
      GeneralPaperControlMaterializationStorage.gridWord x.m (alphabet x).lambda x.k x.Qv≤size x := by
  have hk := (GeneralPaperSourcePreparationEnvelope.base x.m (alphabet x).lambda x.k x.Qv).1
  dsimp only
  unfold size core
  omega

theorem power_columns (x : Input) : (GeneralPaperPowerPrecision.prepare (alphabet x).lambda x.k).columns+1≤size x := by
  have h := (GeneralPaperSourcePreparationControls.metadata x.m (alphabet x).lambda x.k x.Qv).columns
  have hr := (construction_ranges x).2.2.1
  omega

theorem grid_size (x : Input) : (GeneralPaperProfitParameters.prepare x.m (alphabet x).lambda x.k x.Qv).grid.size+1≤size x := by
  have h := GeneralPaperProfitGridPrepare.size_bound
    (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).qProf
    (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).width
    (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).exponent
  have hr := (construction_ranges x).2.2.2.1
  change _≤gridCount x at h
  change (GeneralPaperProfitGridPrepare.prepare
    (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).qProf
    (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).width
    (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).exponent).size+1≤size x
  omega

theorem grid_height (x : Input) : (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).exponent+1≤size x := by
  have h := (GeneralPaperSourcePreparationControls.metadata x.m (alphabet x).lambda x.k x.Qv).exponent
  have hr := (construction_ranges x).2.2.1
  omega

theorem front_depth (x : Input) : (GeneralPaperProxyParameters.prepare x.m x.k).gridBits+6≤size x := by
  have h := (GeneralPaperPrecallControlWord.root_controls x.m x.k).1
  unfold size core
  omega

end Blotto.GeneralPaperFastDriverIndexReference
