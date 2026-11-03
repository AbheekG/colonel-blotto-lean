import Blotto.GeneralPaperNativeSourceRealPhaseRates

/-! The complete native source arithmetic profile has the paper's two-term
real-RAM rate. Logarithms depend only on constructed source parameters, with
no original-ratio encoding-height factor. Epoch and round powers stay separate. -/
namespace Blotto.GeneralPaperSharpSourceRealRate
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperNativeSourceRates
open GeneralPaperSourceRateAlgebra GeneralPaperNativeSourceRealPhaseRates
open GeneralPaperSourceCoreLogBound GeneralPaperCodeAlphabet
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def roundProfile (m k Qv : ℕ) (a : Alphabet) : ℕ :=
  let p := GeneralPaperProfitParameters.prepare m a.lambda k Qv
  GeneralPaperRoundPrice.arithmeticProfile m a.lambda k Qv p.grid.size p.grid.depth p.parameters.height p.parameters.leafCount

def background (m k Qv : ℕ) (a : Alphabet) : ℕ :=
  let t := GeneralPaperTrajectoryParameters.prepare a.lambda k
  GeneralPaperTreeEpochPreparation.arithmeticProfile m k Qv a+
    GeneralPaperEpochInitialFamilyPrice.arithmeticProfile m k+(t.period*256+256)+128+
    GeneralPaperForestUpdatePrice.arithmeticProfile m a.lambda k Qv+256+128+
    GeneralPaperTrajectoryAppendPrice.arithmeticProfile t.period+256

theorem step_split (m k Qv : ℕ) (a : Alphabet) :
    GeneralPaperGeometricSourceStepPrice.arithmeticProfile m k Qv a=background m k Qv a+
      (GeneralPaperTrajectoryParameters.prepare a.lambda k).period*roundProfile m k Qv a := by
  unfold GeneralPaperGeometricSourceStepPrice.arithmeticProfile GeneralPaperOuterEpochPrice.arithmeticProfile
    GeneralPaperOuterEpochPrice.localArithmeticProfile GeneralPaperLocalEpochPrice.arithmeticProfile background roundProfile
  dsimp only
  ring

def backgroundCertificate : Certificate (fun x => background x.m x.k x.Qv (alphabet x)) := by
  have hp : Rated (fun x => GeneralPaperTreeEpochPreparation.arithmeticProfile x.m x.k x.Qv (alphabet x)) 1 1 1 :=
    preparationCertificate.bound
  have hf : Rated (fun x => GeneralPaperForestUpdatePrice.arithmeticProfile x.m (alphabet x).lambda x.k x.Qv) 1 1 1 :=
    forestCertificate.bound
  have hi : Rated (fun x => GeneralPaperEpochInitialFamilyPrice.arithmeticProfile x.m x.k) 1 0 1 :=
    localInitialCertificate.bound
  have ha : Rated (fun x => GeneralPaperTrajectoryAppendPrice.arithmeticProfile
      (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).period) 0 0 1 := appendCertificate.bound
  refine ⟨_,_,_,by
    dsimp only [background]
    fun_prop⟩

theorem background_degrees : (backgroundCertificate.fields,backgroundCertificate.symbols,backgroundCertificate.accuracy)=(1,1,1) := rfl

def sourceRate (x : Input) : ℕ := monomial 1 2 2 x+monomial 1 1 4 x

theorem full_profile_soft : Soft sourceRate (fun x => GeneralPaperGeometricSourcePrice.arithmeticProfile
    x.m x.k x.Qv (alphabet x) (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs) := by
  have hi : Rated (fun x => GeneralPaperForestInitialPrice.arithmeticProfile x.m+256) 1 0 0 := initialCertificate.bound
  have hb : Rated (fun x => background x.m x.k x.Qv (alphabet x)) 1 1 1 := backgroundCertificate.bound
  have hr : Rated (fun x => roundProfile x.m x.k x.Qv (alphabet x)) 1 0 2 := roundCertificate.bound
  have hfirst := add_same (weaken hi (by decide : 1≤1) (by decide : 0≤2) (by decide : 0≤2))
    (GeneralPaperSourceRateAlgebra.mul _ _ 0 1 1 1 1 1 GeneralPaperSharpSourceBitRate.epoch_rate hb)
  have hsecond := GeneralPaperSourceRateAlgebra.mul _ _ 0 1 2 1 0 2 GeneralPaperSharpSourceBitRate.rows_rate hr
  have hall := GeneralPaperSourceSoftBounds.add hfirst hsecond
  apply dominated hall
  intro x
  dsimp only [GeneralPaperGeometricSourcePrice.arithmeticProfile]
  rw [step_split,GeneralPaperTrajectoryParameters.rows_product]
  exact le_of_eq (by ring)

theorem full_core_bound : ∃ A e : ℕ,∀ x,
    GeneralPaperGeometricSourcePrice.arithmeticProfile x.m x.k x.Qv (alphabet x)
      (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs≤A*sourceRate x*(coreLog x)^e :=
  remove_unused_height full_profile_soft (fun _ => rfl) (fun _ => rfl)

theorem profile_prefix_mono (m k Qv : ℕ) (a : Alphabet) {count limit : ℕ} (h : count≤limit) :
    GeneralPaperGeometricSourcePrice.arithmeticProfile m k Qv a count≤
      GeneralPaperGeometricSourcePrice.arithmeticProfile m k Qv a limit := by
  unfold GeneralPaperGeometricSourcePrice.arithmeticProfile
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem prefix_profile_bound : ∃ A e : ℕ,∀ (x : Input) (count : ℕ),
    count≤(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs →
    GeneralPaperGeometricSourcePrice.arithmeticProfile x.m x.k x.Qv (alphabet x) count≤A*sourceRate x*(coreLog x)^e := by
  rcases full_core_bound with ⟨A,e,hA⟩
  exact ⟨A,e,fun x count he => (profile_prefix_mono x.m x.k x.Qv (alphabet x) he).trans (hA x)⟩

def paperRate (x : Input) : ℕ := x.m*(alphabet x).lambda^2*2^(2*x.k)+x.m*(alphabet x).lambda*2^(4*x.k)

theorem nonempty_rate (x : Input) (hm : 1≤x.m) : sourceRate x≤8*paperRate x := by
  have hl := GeneralPaperSourceAlphabetLower.fields_le_lambda x.m x.k
  change x.m≤(alphabet x).lambda at hl
  have hm' : fields x≤2*x.m := by unfold fields; omega
  have hl' : symbols x≤2*(alphabet x).lambda := by unfold symbols; omega
  have h1 := Nat.mul_le_mul_right ((accuracy x)^2) (Nat.mul_le_mul hm' (Nat.pow_le_pow_left hl' 2))
  have h2 := Nat.mul_le_mul_right ((accuracy x)^4) (Nat.mul_le_mul hm' hl')
  have hp := Nat.add_le_add h1 h2
  have he : (2*x.m)*(2*(alphabet x).lambda)^2*(accuracy x)^2+(2*x.m)*(2*(alphabet x).lambda)*(accuracy x)^4=
      8*(x.m*(alphabet x).lambda^2*(accuracy x)^2)+4*(x.m*(alphabet x).lambda*(accuracy x)^4) := by ring
  have hb : 8*(x.m*(alphabet x).lambda^2*(accuracy x)^2)+4*(x.m*(alphabet x).lambda*(accuracy x)^4)≤
      8*(x.m*(alphabet x).lambda^2*(accuracy x)^2+x.m*(alphabet x).lambda*(accuracy x)^4) := by
    nlinarith only [Nat.zero_le (x.m*(alphabet x).lambda*(accuracy x)^4)]
  apply (show sourceRate x≤_ by simpa only [sourceRate,monomial,pow_one] using hp).trans
  rw [he]
  apply hb.trans_eq
  simp only [paperRate,accuracy,←pow_mul,Nat.mul_comm x.k 2,Nat.mul_comm x.k 4]

theorem paper_prefix_bound : ∃ A e : ℕ,∀ (x : Input) (count : ℕ),1≤x.m →
    count≤(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs →
    GeneralPaperGeometricSourcePrice.arithmeticProfile x.m x.k x.Qv (alphabet x) count≤A*paperRate x*(coreLog x)^e := by
  rcases prefix_profile_bound with ⟨A,e,hA⟩
  refine ⟨8*A,e,?_⟩
  intro x count hm he
  apply (hA x count he).trans
  exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left A (nonempty_rate x hm))).trans_eq (by ring)

end Blotto.GeneralPaperSharpSourceRealRate
