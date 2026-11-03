import Blotto.GeneralPaperPhysicalResponseSourcePrice

/-! Include all actual physical checks and the single shift construction
in the full sharp source bounds. Both source tradeoffs remain separate;
the real logarithm excludes the original ratio's height. -/
namespace Blotto.GeneralPaperPhysicalResponseSourceRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperNativeSourceRates
open GeneralPaperSourceRateAlgebra GeneralPaperSourceStorageRates GeneralPaperSummaryArrayExecution
open GeneralPaperSourceCoreLogBound GeneralPaperCatalogueShared
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384

def fullBitExtra (C d W : ℕ) (x : Input) : ℕ :=
  GeneralPaperPhysicalResponseSourceCache.bitExtra (GeneralPaperFastRationalMajorant.model C d) W
    (GeneralPaperProxyParameters.prepare x.m x.k).qbar ((alphabet x).lambda+1) (alphabet x)
    (prepare (alphabet x) x.k x.Qv x.weights 0 0) (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs

def fullArithmeticExtra (x : Input) : ℕ :=
  GeneralPaperPhysicalResponseSourceCache.arithmeticExtra (alphabet x)
    (prepare (alphabet x) x.k x.Qv x.weights 0 0) (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs

def bitCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate (fun x => fullBitExtra C d (W x) x) := by
  have hp := GeneralPaperPhysicalResponseRates.bit_rate C d W hW
  have hs := (GeneralPaperPhysicalResponseRates.shiftPriceCertificate C d W hW).bound
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw : Small W := of_tight hW
  refine ⟨_,_,_,by
    unfold fullBitExtra GeneralPaperPhysicalResponseSourceCache.bitExtra GeneralPaperPhysicalResponseSourceExecution.bitExtra
    dsimp only [prepare]
    unfold arrayWord
    source_space⟩

theorem bit_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((bitCertificate C d W hW).fields,(bitCertificate C d W hW).symbols,(bitCertificate C d W hW).accuracy)=(1,3,2) := rfl

def arithmeticCertificate : Certificate fullArithmeticExtra := by
  have hp := GeneralPaperPhysicalResponseRates.arithmeticCertificate.bound
  refine ⟨_,_,_,by
    unfold fullArithmeticExtra GeneralPaperPhysicalResponseSourceCache.arithmeticExtra
      GeneralPaperPhysicalResponseSourceExecution.arithmeticExtra
    dsimp only [prepare]
    source_space⟩

theorem arithmetic_degrees :
    (arithmeticCertificate.fields,arithmeticCertificate.symbols,arithmeticCertificate.accuracy)=(1,2,2) := rfl

def bitProfile (C d W : ℕ) (x : Input) : ℕ :=
  GeneralPaperFastSourceMajorant.profile C d W x.m x.k x.Qv (alphabet x)
    (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs+fullBitExtra C d W x

def arithmeticProfile (x : Input) : ℕ :=
  GeneralPaperGeometricSourcePrice.arithmeticProfile x.m x.k x.Qv (alphabet x)
    (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs+fullArithmeticExtra x

theorem bit_soft (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Soft GeneralPaperSharpSourceBitRate.sourceRate (fun x => bitProfile C d (W x) x) := by
  have he := rate_mono (bitCertificate C d W hW).bound
    (fun x => Nat.le_add_right (monomial 1 3 2 x) (monomial 1 2 4 x))
  exact add_same (GeneralPaperSharpSourceBitRate.full_profile_soft C d W hW) he

theorem arithmetic_soft : Soft GeneralPaperSharpSourceRealRate.sourceRate arithmeticProfile := by
  have he := rate_mono arithmeticCertificate.bound
    (fun x => Nat.le_add_right (monomial 1 2 2 x) (monomial 1 1 4 x))
  exact add_same GeneralPaperSharpSourceRealRate.full_profile_soft he

theorem real_bound : ∃ A e : ℕ,∀ x,arithmeticProfile x≤
    A*GeneralPaperSharpSourceRealRate.sourceRate x*(coreLog x)^e :=
  remove_unused_height arithmetic_soft (fun _ => rfl) (fun _ => rfl)

theorem bit_bound (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : ∃ A e : ℕ,∀ x,bitProfile C d (W x) x≤
    A*GeneralPaperSharpSourceBitRate.sourceRate x*(logSize x)^e := bit_soft C d W hW

theorem paper_real_bound : ∃ A e : ℕ,∀ x,1≤x.m →arithmeticProfile x≤
    A*GeneralPaperSharpSourceRealRate.paperRate x*(coreLog x)^e := by
  rcases real_bound with ⟨A,e,hA⟩
  refine ⟨8*A,e,?_⟩
  intro x hm
  exact (hA x).trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left A
    (GeneralPaperSharpSourceRealRate.nonempty_rate x hm))).trans_eq (by ring))

theorem paper_bit_bound (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : ∃ A e : ℕ,∀ x,1≤x.m →bitProfile C d (W x) x≤
    A*GeneralPaperSharpSourceBitRate.paperRate x*(logSize x)^e := by
  rcases bit_bound C d W hW with ⟨A,e,hA⟩
  refine ⟨16*A,e,?_⟩
  intro x hm
  exact (hA x).trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left A
    (GeneralPaperSharpSourceBitRate.nonempty_rate x hm))).trans_eq (by ring))

end Blotto.GeneralPaperPhysicalResponseSourceRates
