import Blotto.GeneralPaperBudgetCandidateStorage

/-! Retained affine field/table owners and full current pair/budget
candidate temporaries. Their source degree is (2,0,2), within the checked
refinement reservation (3,0,4). Batch list/append/iterator frames and the
remaining compiler phases are separate joins. -/
namespace Blotto.GeneralPaperSourceCrossingOperandStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperCompilerReferenceGrowth
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def profile (model : RationalCostModel) (W m K S R : ℕ) : ℕ :=
  GeneralPaperAffineWitnessStorage.tableProfile W S K m R+GeneralPaperAffineWitnessStorage.fieldProfile W K S R+
    GeneralPaperAffineCandidatePairStorage.profile model W m K S R+GeneralPaperBudgetCandidateStorage.profile model W m K S R

theorem native_pair {S K : ℕ} (model : RationalCostModel) (W D E m X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n+1≤m)
    (field : GeneralPaperRayAffineScoreStep.Field K) (previous : GeneralPaperRayAffineScoreStep.Table S K)
    (hf : GeneralPaperRayAffineDPSize.FieldBounded D E X V field) (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n previous)
    (hScores : ∀ l,(field.read l).1≤S) (s : Fin (S+1)) (a b : Fin K) :
    GeneralPaperAffineWitnessStorage.tableFoot W previous+GeneralPaperAffineWitnessStorage.fieldFoot W field+
      GeneralPaperAffineCandidatePairStorage.window model W field previous s a b≤profile model W m K S (GeneralPaperRayUniformSize.width D E m X V P) := by
  have ht := GeneralPaperAffineWitnessStorage.table_bound W D E X V n m P hD hE (by omega) previous hp
  have hField := GeneralPaperAffineWitnessStorage.field_bound W D E X V m P S hD hE (by omega) field hf hScores
  have hp := GeneralPaperAffineCandidatePairStorage.bounded model W D E m X V P n hD hE hn field previous hf hp hScores s a b
  unfold profile
  omega

theorem native_budget {S K : ℕ} (model : RationalCostModel) (W D E m X V P n : ℕ) (hD : 0<D) (hE : 0<E) (hn : n≤m)
    (table : GeneralPaperRayAffineScoreStep.Table S K) (hp : GeneralPaperRayAffineDPSize.TableBounded D E X V n table)
    (h : ℕ) (hh : h≤S) (beta : ℚ) (hb : GeneralPaperRayRationalBound.Bounded D P beta) (s : Fin (S+1)) :
    GeneralPaperAffineWitnessStorage.tableFoot W table+GeneralPaperBudgetCandidateStorage.window model W table h beta s≤
      profile model W m K S (GeneralPaperRayUniformSize.width D E m X V P) := by
  have ht := GeneralPaperAffineWitnessStorage.table_bound W D E X V n m P hD hE hn table hp
  have hc := GeneralPaperBudgetCandidateStorage.bounded model W D E m X V P n hD hE hn table hp h hh beta hb s
  unfold profile
  omega

theorem height_mono (model : RationalCostModel) (W m K S R H : ℕ) (hR : R≤H) : profile model W m K S R≤profile model W m K S H := by
  unfold profile GeneralPaperAffineWitnessStorage.tableProfile GeneralPaperAffineWitnessStorage.fieldProfile
    GeneralPaperAffineCandidatePairStorage.profile GeneralPaperBudgetCandidateStorage.profile GeneralPaperAffineCandidateStorage.expressionProfile
    GeneralPaperAffineCandidateStorage.profile GeneralPaperAffineArithmeticStorage.optionalProfile GeneralPaperAffineArithmeticStorage.crossingProfile
    GeneralPaperAffineArithmeticStorage.addProfile GeneralPaperAffineCandidatePairStorage.metadataCap GeneralPaperAffineCandidateStorage.metadataCap
    GeneralPaperBudgetCandidateStorage.metadataCap GeneralPaperAffineArithmeticStorage.addCap GeneralPaperAffineArithmeticStorage.crossingCap
    GeneralPaperAffineWitnessStorage.optionChoiceProfile GeneralPaperAffineWitnessStorage.choiceProfile GeneralPaperAffineWitnessStorage.optionAffineProfile
    GeneralPaperAffineArithmeticStorage.rootProfile GeneralPaperAffineWitnessStorage.affineProfile GeneralPaperEncodedScalarStorage.natBits
  gcongr <;> (apply model.monotone; omega)

theorem scaling (model : RationalCostModel) (m K S R : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => profile model W m K S R) := by
  unfold profile GeneralPaperAffineWitnessStorage.tableProfile GeneralPaperAffineWitnessStorage.fieldProfile
    GeneralPaperAffineCandidatePairStorage.profile GeneralPaperBudgetCandidateStorage.profile GeneralPaperAffineCandidateStorage.expressionProfile
    GeneralPaperAffineCandidateStorage.profile GeneralPaperAffineArithmeticStorage.optionalProfile GeneralPaperAffineArithmeticStorage.crossingProfile
    GeneralPaperAffineArithmeticStorage.addProfile GeneralPaperAffineCandidatePairStorage.metadataCap GeneralPaperAffineCandidateStorage.metadataCap
    GeneralPaperBudgetCandidateStorage.metadataCap GeneralPaperAffineArithmeticStorage.addCap GeneralPaperAffineArithmeticStorage.crossingCap
    GeneralPaperAffineWitnessStorage.optionChoiceProfile GeneralPaperAffineWitnessStorage.choiceProfile GeneralPaperAffineWitnessStorage.optionAffineProfile
    GeneralPaperAffineArithmeticStorage.rootProfile GeneralPaperAffineWitnessStorage.affineProfile GeneralPaperEncodedScalarStorage.natBits
  fun_prop

theorem model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m K S R : ℕ) :
    profile actual W m K S R≤profile upper W m K S R := by
  unfold profile GeneralPaperAffineWitnessStorage.tableProfile GeneralPaperAffineWitnessStorage.fieldProfile
    GeneralPaperAffineCandidatePairStorage.profile GeneralPaperBudgetCandidateStorage.profile GeneralPaperAffineCandidateStorage.expressionProfile
    GeneralPaperAffineCandidateStorage.profile GeneralPaperAffineArithmeticStorage.optionalProfile GeneralPaperAffineArithmeticStorage.crossingProfile
    GeneralPaperAffineArithmeticStorage.addProfile GeneralPaperAffineCandidatePairStorage.metadataCap GeneralPaperAffineCandidateStorage.metadataCap
    GeneralPaperBudgetCandidateStorage.metadataCap GeneralPaperAffineArithmeticStorage.addCap GeneralPaperAffineArithmeticStorage.crossingCap
    GeneralPaperAffineWitnessStorage.optionChoiceProfile GeneralPaperAffineWitnessStorage.choiceProfile GeneralPaperAffineWitnessStorage.optionAffineProfile
    GeneralPaperAffineArithmeticStorage.rootProfile GeneralPaperAffineWitnessStorage.affineProfile GeneralPaperEncodedScalarStorage.natBits
  gcongr <;> exact h _

def sourceProfile (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  profile model W m (GeneralPaperProxyParameters.prepare m k).K (GeneralPaperProxyParameters.prepare m k).S
    (GeneralPaperSourceRayStorageWidth.width m k)

def certificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => sourceProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
  have hR := GeneralPaperSourceSharpOperandRates.ray_width
  have hsR := GeneralPaperSourceRayStorageRates.width_small
  refine ⟨_,_,_,by
    unfold sourceProfile profile GeneralPaperAffineWitnessStorage.tableProfile
      GeneralPaperAffineWitnessStorage.fieldProfile GeneralPaperAffineCandidatePairStorage.profile GeneralPaperBudgetCandidateStorage.profile
      GeneralPaperAffineCandidateStorage.expressionProfile GeneralPaperAffineCandidateStorage.profile GeneralPaperAffineArithmeticStorage.optionalProfile
      GeneralPaperAffineArithmeticStorage.crossingProfile GeneralPaperAffineArithmeticStorage.addProfile GeneralPaperAffineCandidatePairStorage.metadataCap
      GeneralPaperAffineCandidateStorage.metadataCap GeneralPaperBudgetCandidateStorage.metadataCap GeneralPaperAffineArithmeticStorage.addCap
      GeneralPaperAffineArithmeticStorage.crossingCap GeneralPaperAffineWitnessStorage.optionChoiceProfile GeneralPaperAffineWitnessStorage.choiceProfile
      GeneralPaperAffineWitnessStorage.optionAffineProfile GeneralPaperAffineArithmeticStorage.rootProfile GeneralPaperAffineWitnessStorage.affineProfile
      GeneralPaperEncodedScalarStorage.natBits
    dsimp only [GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((certificate C d W hW).fields,(certificate C d W hW).symbols,(certificate C d W hW).accuracy)=(2,0,2) := rfl

theorem actual_rate {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d)
    (W : Input → ℕ) (hW : Tight W) : Rated (fun x => sourceProfile actual (W x) x.m x.k) 2 0 2 :=
  GeneralPaperSourceSoftBounds.dominated (certificate C d W hW).bound
    (fun x => model_mono actual (GeneralPaperFastRationalMajorant.model C d) (GeneralPaperFastRationalMajorant.dominates hg) (W x) _ _ _ _)

def reservation (model : RationalCostModel) (W m k : ℕ) : ℕ :=
  GeneralPaperSourceCrossingRefinementRates.reservation model W m k+sourceProfile model W m k

def reservationCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k) := by
  have hOld := (GeneralPaperSourceCrossingRefinementRates.reservationCertificate C d W hW).bound
  have hOperands := (certificate C d W hW).bound
  refine ⟨_,_,_,by unfold reservation; source_space⟩

theorem reservation_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((reservationCertificate C d W hW).fields,(reservationCertificate C d W hW).symbols,
      (reservationCertificate C d W hW).accuracy)=(3,0,4) := rfl

theorem reservation_scaling (model : RationalCostModel) (m k : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => reservation model W m k) := by
  have ho := GeneralPaperSourceCrossingRefinementRates.reservation_scaling model m k
  have hp := scaling model m (GeneralPaperProxyParameters.prepare m k).K (GeneralPaperProxyParameters.prepare m k).S (GeneralPaperSourceRayStorageWidth.width m k)
  unfold reservation sourceProfile
  fun_prop

theorem reservation_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k : ℕ) :
    reservation actual W m k≤reservation upper W m k :=
  Nat.add_le_add (GeneralPaperSourceCrossingRefinementRates.reservation_mono actual upper h W m k) (model_mono actual upper h W _ _ _ _)

theorem actual_reservation_rate {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d)
    (W : Input → ℕ) (hW : Tight W) : Rated (fun x => reservation actual (W x) x.m x.k) 3 0 4 :=
  GeneralPaperSourceSoftBounds.dominated (reservationCertificate C d W hW).bound
    (fun x => reservation_mono actual (GeneralPaperFastRationalMajorant.model C d) (GeneralPaperFastRationalMajorant.dominates hg) (W x) x.m x.k)

theorem reservation_at_one_small (C d : ℕ) : Small (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) 1 x.m x.k) := by
  apply GeneralPaperSourceRowsStorageRates.soft_small (reservationCertificate C d (fun _ => 1) (tight_constant 1)).bound
  unfold monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
  fun_prop

theorem actual_common_word {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d) :
    ∃ A e : ℕ,∀ x,reservation actual (GeneralPaperCompilerReference.width C d x) x.m x.k≤
      A*(x.m+1)^3*2^(4*x.k)*(logSize x)^e := by
  rcases actual_reservation_rate hg (GeneralPaperCompilerReference.width C d) (width_tight C d) with ⟨A,e,hA⟩
  refine ⟨A,e,?_⟩
  intro x
  have he : (GeneralPaperNativeSourceRates.accuracy x)^4=2^(4*x.k) := by
    simp only [GeneralPaperNativeSourceRates.accuracy,←pow_mul,Nat.mul_comm x.k 4]
  simpa only [monomial,pow_zero,Nat.mul_one,GeneralPaperNativeSourceRates.fields,he,Nat.mul_assoc] using hA x

end Blotto.GeneralPaperSourceCrossingOperandStorageRates
