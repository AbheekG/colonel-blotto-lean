import Blotto.GeneralPaperSourceLifetimeRates

/-! The original ratio is retained once. Its height contributes additively
to classifier storage; only constructed control frames incur a depth factor.
The fast primitive scratch uses its actual operand word and proved growth. -/
namespace Blotto.GeneralPaperClassifierSpaceRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperNativeSourceRates
open GeneralPaperSourceRateAlgebra GeneralPaperSourceStorageRates
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384

def rate (x : Input) : ℕ := x.B+1+monomial 1 2 2 x

theorem positive (x : Input) : 1≤rate x := by unfold rate; omega

theorem lift_source {f : Input → ℕ} (hf : Rated f 1 2 2) : Soft rate f :=
  rate_mono hf (fun x => by unfold rate; omega)

theorem input_rate : Soft rate Input.B :=
  rate_mono (identity Input.B) (fun x => by unfold rate; omega)

theorem affine {f : Input → ℕ} (a : ℕ) (hf : Rated f 1 2 2) :
    Soft rate (fun x => a*x.B+f x) :=
  add_same (poly_mul_rate (poly_constant a) input_rate) (lift_source hf)

def quotientWidth (x : Input) (B : ℕ) : ℕ :=
  1+2*GeneralPaperBoundedQuotient.heightBudget
    (B+binaryWordWidth (GeneralPaperProxyParameters.prepare x.m x.k).Qg) 1
    ((GeneralPaperProxyParameters.prepare x.m x.k).gridBits+1)

def locationWidth (x : Input) (B : ℕ) : ℕ :=
  GeneralPaperProxyQuotientPrice.envelope (GeneralPaperPrecallCachePrice.specification x.m x.k) B

def selectionWidth (x : Input) (B : ℕ) : ℕ :=
  GeneralPaperSelectionPoints.width (GeneralPaperProxyParameters.prepare x.m x.k).Qg B

def widthCertificate : Certificate (fun x => quotientWidth x 0+locationWidth x 0+selectionWidth x 0) := by
  refine ⟨_,_,_,by
    unfold quotientWidth locationWidth selectionWidth GeneralPaperBoundedQuotient.heightBudget
      GeneralPaperProxyQuotientPrice.envelope GeneralPaperSelectionPoints.width
    dsimp only [GeneralPaperPrecallCachePrice.specification]
    source_space⟩

theorem width_degrees :
    (widthCertificate.fields,widthCertificate.symbols,widthCertificate.accuracy)=(0,1,0) := rfl

theorem width_zero : Rated (fun x => quotientWidth x 0+locationWidth x 0+selectionWidth x 0) 1 2 2 :=
  weaken widthCertificate.bound (by decide) (by decide) (by decide)

theorem quotient_affine (x : Input) (B : ℕ) : quotientWidth x B=2*B+quotientWidth x 0 := by
  unfold quotientWidth GeneralPaperBoundedQuotient.heightBudget
  omega

theorem location_affine (x : Input) (B : ℕ) : locationWidth x B=4*B+locationWidth x 0 := by
  unfold locationWidth GeneralPaperProxyQuotientPrice.envelope
  omega

theorem selection_affine (x : Input) (B : ℕ) : selectionWidth x B=4*B+selectionWidth x 0 := by
  unfold selectionWidth GeneralPaperSelectionPoints.width
  omega

theorem quotient_soft : Soft rate (fun x => quotientWidth x x.B) := by
  have h : Rated (fun x => quotientWidth x 0) 1 2 2 := dominated width_zero (fun x => by omega)
  have he : (fun x => quotientWidth x x.B)=(fun x => 2*x.B+quotientWidth x 0) :=
    funext (fun x => quotient_affine x x.B)
  rw [he]
  exact affine 2 h

theorem location_soft : Soft rate (fun x => locationWidth x x.B) := by
  have h : Rated (fun x => locationWidth x 0) 1 2 2 := dominated width_zero (fun x => by omega)
  have he : (fun x => locationWidth x x.B)=(fun x => 4*x.B+locationWidth x 0) :=
    funext (fun x => location_affine x x.B)
  rw [he]
  exact affine 4 h

theorem selection_soft : Soft rate (fun x => selectionWidth x x.B) := by
  have h : Rated (fun x => selectionWidth x 0) 1 2 2 := dominated width_zero (fun x => by omega)
  have he : (fun x => selectionWidth x x.B)=(fun x => 4*x.B+selectionWidth x 0) :=
    funext (fun x => selection_affine x x.B)
  rw [he]
  exact affine 4 h

@[fun_prop]
theorem quotient_small : Small (fun x => quotientWidth x x.B) := by
  unfold quotientWidth GeneralPaperBoundedQuotient.heightBudget
  fun_prop

@[fun_prop]
theorem location_small : Small (fun x => locationWidth x x.B) := by
  unfold locationWidth GeneralPaperProxyQuotientPrice.envelope
  dsimp only [GeneralPaperPrecallCachePrice.specification]
  fun_prop

@[fun_prop]
theorem selection_small : Small (fun x => selectionWidth x x.B) := by
  unfold selectionWidth GeneralPaperSelectionPoints.width
  fun_prop

def zeroCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x =>
    GeneralPaperClassifierConstructionStorage.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k 0) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw : Small W := of_tight hW
  refine ⟨_,_,_,by
    unfold GeneralPaperClassifierConstructionStorage.profile GeneralPaperProxyLocationStorage.profile
      GeneralPaperQuotientConstructionStorage.frameCap GeneralPaperQuotientConstructionStorage.localCap
      GeneralPaperBoundedQuotient.heightBudget GeneralPaperProxyQuotientPrice.word
      GeneralPaperProxyQuotientPrice.envelope GeneralPaperCFOperandPrice.width
      GeneralPaperSelectionConstructionStorage.profile GeneralPaperClassifierResultStorage.profile
      GeneralPaperSelectionPoints.width GeneralPaperPrecallCacheStorage.payload
    dsimp only [GeneralPaperFastRationalMajorant.model,GeneralPaperPrecallCachePrice.specification]
    source_space⟩

theorem zero_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((zeroCertificate C d W hW).fields,(zeroCertificate C d W hW).symbols,
      (zeroCertificate C d W hW).accuracy)=(0,2,0) := rfl

theorem profile_split_bound (C d : ℕ) (W : Input → ℕ) (x : Input) :
    GeneralPaperClassifierConstructionStorage.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.B≤
      GeneralPaperClassifierConstructionStorage.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k 0+
      228*x.B+8*GeneralPaperFastRationalModel.charge (C+1) d (quotientWidth x x.B)+
      4*GeneralPaperFastRationalModel.charge (C+1) d (locationWidth x x.B)+
      512*GeneralPaperFastRationalModel.charge (C+1) d (selectionWidth x x.B) := by
  unfold GeneralPaperClassifierConstructionStorage.profile GeneralPaperProxyLocationStorage.profile
    GeneralPaperQuotientConstructionStorage.localCap GeneralPaperSelectionConstructionStorage.profile
    quotientWidth locationWidth selectionWidth GeneralPaperProxyQuotientPrice.envelope
    GeneralPaperBoundedQuotient.heightBudget GeneralPaperSelectionPoints.width
  dsimp only [GeneralPaperFastRationalMajorant.model,GeneralPaperPrecallCachePrice.specification]
  omega

theorem classifier_soft (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Soft rate (fun x =>
    GeneralPaperClassifierConstructionStorage.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.B) := by
  have hz := lift_source (weaken (zeroCertificate C d W hW).bound
    (by decide : 0≤1) (by decide : 2≤2) (by decide : 0≤2))
  have hB := poly_mul_rate (poly_constant 228) input_rate
  have hq := poly_mul_rate (poly_constant 8) (charge_preserves (C+1) d quotient_soft quotient_small)
  have hl := poly_mul_rate (poly_constant 4) (charge_preserves (C+1) d location_soft location_small)
  have hs := poly_mul_rate (poly_constant 512) (charge_preserves (C+1) d selection_soft selection_small)
  exact dominated (add_same (add_same (add_same (add_same hz hB) hq) hl) hs) (profile_split_bound C d W)

end Blotto.GeneralPaperClassifierSpaceRates
