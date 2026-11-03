import Blotto.GeneralPaperCachedBitPairStorage

/-! The actual cached parent preserves degree (3,0,4) and additive input
ratio height. Its fixed scalar frames have degree (1,0,1). All prior
reservations remain summed. No exponential alphabet value is treated as
a polynomially bounded scalar; only its proved encoded width is used. -/
namespace Blotto.GeneralPaperCachedBitPairStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperCachedPreparationScalarStorage GeneralPaperCachedBitPairStorage
open GeneralPaperReferenceScaling
open GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

@[fun_prop]
theorem price_scaling (model : RationalCostModel) (C d m k Qv : ℕ) :
    Scale (fun W => price model C d W m k Qv) := by
  have h := GeneralPaperCompleteCallerReferenceScaling.prepared_price model C d m k Qv
  dsimp only [price,decodePrice,sharedPrice]
  fun_prop

@[fun_prop]
theorem scaling (model : RationalCostModel) (C d m k Qv B : ℕ) :
    Scale (fun W => profile model C d W m k Qv B) := by
  have h := GeneralPaperCompleteCallerReferenceScaling.prepared_profile model C d m k Qv B
  have hp := price_scaling model C d m k Qv
  dsimp only [profile,decodeProfile,decodeCap,decodePrice,sharedProfile,sharedCap,sharedPrice,metadataCap,natBits]
  fun_prop

theorem price_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (C d W m k Qv : ℕ) :
    price actual C d W m k Qv≤price upper C d W m k Qv := by
  have hp := GeneralPaperSourcePreparedPairOwnerRates.price_mono actual upper h C d W m k Qv
  dsimp only [price,decodePrice,sharedPrice]
  gcongr <;> exact h _

theorem model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (C d W m k Qv B : ℕ) :
    profile actual C d W m k Qv B≤profile upper C d W m k Qv B := by
  have hp := price_mono actual upper h C d W m k Qv
  have hOld := GeneralPaperSourcePreparedPairOwnerRates.model_mono actual upper h C d W m k Qv B
  dsimp only [profile,decodeProfile,decodeCap,decodePrice,sharedProfile,sharedCap,sharedPrice,metadataCap,natBits]
  gcongr <;> exact h _

@[fun_prop]
theorem scalar_price_small (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Small (fun x => sharedPrice (GeneralPaperFastRationalMajorant.model C d) (W x) x.k (precision x.m x.k) (alphabet x)) := by
  have hw := of_tight hW
  dsimp only [sharedPrice,GeneralPaperSharedSpanPrice.width,GeneralPaperSharedWidthPrice.width,precision,
    GeneralPaperFastRationalMajorant.model]
  fun_prop

@[fun_prop]
theorem price_small (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Small (fun x => price (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m x.k x.Qv) := by
  have hw := of_tight hW
  have hOld := GeneralPaperSourcePreparedPairOwnerRates.price_small C d W hW
  have hShared := scalar_price_small C d W hW
  dsimp only [price,decodePrice,decodeWidth,GeneralPaperFastRationalMajorant.model]
  fun_prop

def decodeCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate
    (fun x => decodeProfile (GeneralPaperFastRationalMajorant.model C d) (W x) (GeneralPaperProxyParameters.prepare x.m x.k).qbar) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw := of_tight hW
  have hCap := GeneralPaperSourceSharpOperandRates.cap_word
  refine ⟨_,_,_,by
    dsimp only [decodeProfile,decodeWidth,decodeCap,decodePrice,natBits,GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem decode_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((decodeCertificate C d W hW).fields,(decodeCertificate C d W hW).symbols,(decodeCertificate C d W hW).accuracy)=(1,0,1) := rfl

theorem shared_cap_word (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Rated
    (fun x => binaryWordWidth (sharedCap (GeneralPaperFastRationalMajorant.model C d) (W x) x.k (precision x.m x.k) (alphabet x))) 1 0 1 := by
  have hLambda := GeneralPaperSourceSharpOperandRates.alphabet_length
  have hw := of_tight hW
  have hPrice := scalar_price_small C d W hW
  apply GeneralPaperSourceSoftBounds.dominated (g:=fun x => 1+2*(alphabet x).lambda+
    binaryWordWidth (precision x.m x.k)+binaryWordWidth x.k+binaryWordWidth 40+
    binaryWordWidth (sharedPrice (GeneralPaperFastRationalMajorant.model C d) (W x) x.k (precision x.m x.k) (alphabet x))+
    binaryWordWidth (W x))
  · change Rated _ 1 0 1
    dsimp only [precision]
    source_space
  · intro x
    have hC := GeneralPaperSharedSpanPrice.scale_word (alphabet x)
    have h1 := GeneralPaperReferenceScaling.word_add (alphabet x).C (precision x.m x.k)
    have h2 := GeneralPaperReferenceScaling.word_add ((alphabet x).C+precision x.m x.k) x.k
    have h3 := GeneralPaperReferenceScaling.word_add ((alphabet x).C+precision x.m x.k+x.k) 40
    have h4 := GeneralPaperReferenceScaling.word_add ((alphabet x).C+precision x.m x.k+x.k+40)
      (sharedPrice (GeneralPaperFastRationalMajorant.model C d) (W x) x.k (precision x.m x.k) (alphabet x))
    have h5 := GeneralPaperReferenceScaling.word_add ((alphabet x).C+precision x.m x.k+x.k+40+
      sharedPrice (GeneralPaperFastRationalMajorant.model C d) (W x) x.k (precision x.m x.k) (alphabet x)) (W x)
    unfold sharedCap
    omega

def sharedCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate
    (fun x => sharedProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.k (precision x.m x.k) (alphabet x)) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw := of_tight hW
  have hLambda := GeneralPaperSourceSharpOperandRates.alphabet_length
  have hCap := shared_cap_word C d W hW
  refine ⟨_,_,_,by
    dsimp only [sharedProfile,GeneralPaperSharedSpanPrice.width,GeneralPaperSharedWidthPrice.width,precision,natBits,
      GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem shared_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((sharedCertificate C d W hW).fields,(sharedCertificate C d W hW).symbols,(sharedCertificate C d W hW).accuracy)=(1,0,1) := rfl

def certificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate
    (fun x => profile (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m x.k x.Qv 0) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw := of_tight hW
  have hOld := (GeneralPaperSourcePreparedPairOwnerRates.certificate C d W hW).bound
  have hDecode := (decodeCertificate C d W hW).bound
  have hShared := (sharedCertificate C d W hW).bound
  have hp := price_small C d W hW
  refine ⟨_,_,_,by
    dsimp only [profile,metadataCap,natBits,precision]
    source_space⟩

theorem degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((certificate C d W hW).fields,(certificate C d W hW).symbols,(certificate C d W hW).accuracy)=(3,0,4) := rfl

noncomputable def reservation (actual : RationalCostModel) (C d W m k Qv B : ℕ) : ℕ :=
  GeneralPaperSourcePreparedPairOwnerRates.reservation actual C d W m k Qv B+profile actual C d W m k Qv B

@[fun_prop]
theorem reservation_scaling (model : RationalCostModel) (C d m k Qv B : ℕ) :
    Scale (fun W => reservation model C d W m k Qv B) := by
  have hOld := GeneralPaperCompleteCallerReferenceScaling.complete_reservation model C d m k Qv B
  have hNew := scaling model C d m k Qv B
  unfold reservation
  fun_prop

theorem reservation_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (C d W m k Qv B : ℕ) :
    reservation actual C d W m k Qv B≤reservation upper C d W m k Qv B :=
  Nat.add_le_add (GeneralPaperSourcePreparedPairOwnerRates.reservation_mono actual upper h C d W m k Qv B)
    (model_mono actual upper h C d W m k Qv B)

def reservationCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate
    (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m x.k x.Qv 0) := by
  refine ⟨3,0,4,?_⟩
  exact GeneralPaperSourceRateAlgebra.add _ _ 3 0 4 3 0 4
    (GeneralPaperSourcePreparedPairOwnerRates.reservationCertificate C d W hW).bound (certificate C d W hW).bound

theorem affine (model : RationalCostModel) (C d W m k Qv B : ℕ) :
    reservation model C d W m k Qv B=8*B+reservation model C d W m k Qv 0 := by
  unfold reservation
  rw [GeneralPaperSourcePreparedPairOwnerRates.affine]
  unfold profile GeneralPaperSourcePreparedPairOwners.profile
  omega

theorem majorant_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Soft GeneralPaperSourcePreparedPairOwnerRates.rate
    (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m x.k x.Qv x.B) := by
  have hRated : Rated (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m x.k x.Qv 0) 3 0 4 :=
    (reservationCertificate C d W hW).bound
  have hBase : Soft GeneralPaperSourcePreparedPairOwnerRates.rate
      (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m x.k x.Qv 0) :=
    rate_mono hRated (fun x => by unfold GeneralPaperSourcePreparedPairOwnerRates.rate;omega)
  have hInput : Soft GeneralPaperSourcePreparedPairOwnerRates.rate Input.B :=
    rate_mono (GeneralPaperSourceSoftBounds.identity Input.B) (fun x => by unfold GeneralPaperSourcePreparedPairOwnerRates.rate;omega)
  have h := add_same (poly_mul_rate (poly_constant 8) hInput) hBase
  exact GeneralPaperSourceSoftBounds.dominated h (fun x => by rw [affine])

theorem reservation_at_one_small (C d : ℕ) : Small
    (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) C d 1 x.m x.k x.Qv x.B) := by
  apply GeneralPaperSourceRowsStorageRates.soft_small (majorant_rate C d (fun _ => 1) (tight_constant 1))
  unfold GeneralPaperSourcePreparedPairOwnerRates.rate monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
  fun_prop

end Blotto.GeneralPaperCachedBitPairStorageRates
