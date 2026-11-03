import Blotto.GeneralPaperNativeSourcePhaseRates

/-! Join every native iterative-source phase without merging its two different
accuracy/alphabet tradeoffs. This bounds the complete closed source price,
not only its DP calls. The common reference width is constructed beforehand. -/
namespace Blotto.GeneralPaperSharpSourceBitRate
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperNativeSourceRates
open GeneralPaperSourceRateAlgebra GeneralPaperNativeSourcePhaseRates
open GeneralPaperFastRationalModel GeneralPaperCodeAlphabet
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def background (C d W m k Qv : ℕ) (a : Alphabet) : ℕ :=
  let model := GeneralPaperFastRationalMajorant.model C d
  let t := GeneralPaperTrajectoryParameters.prepare a.lambda k
  GeneralPaperTreeEpochPreparation.profile model W m k Qv a+
    GeneralPaperEpochInitialFamilyPrice.profile model.rat W m k+
    (t.period*(256*arrayWord W (t.period+2))+256*arrayWord W (t.period+2))+128*W+
    GeneralPaperForestUpdatePrice.profile model.rat W m a.lambda k Qv+256*W+128*W+
    GeneralPaperTrajectoryAppendPrice.profile W t.rows t.period+256*arrayWord W (t.epochs+2)

theorem step_split (C d W m k Qv : ℕ) (a : Alphabet) :
    GeneralPaperSelectorRefinedSourcePrice.stepProfile (GeneralPaperFastRationalMajorant.model C d)
      C d W m k Qv a=background C d W m k Qv a+
        (GeneralPaperTrajectoryParameters.prepare a.lambda k).period*
          GeneralPaperSelectorRefinedSourcePrice.roundProfile (GeneralPaperFastRationalMajorant.model C d)
            C d W m a.lambda k Qv := by
  unfold GeneralPaperSelectorRefinedSourcePrice.stepProfile GeneralPaperSelectorRefinedSourcePrice.outerProfile
    GeneralPaperSelectorRefinedSourcePrice.localProfile background
  dsimp only
  ring

def backgroundCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Certificate (fun x => background C d (W x) x.m x.k x.Qv (alphabet x)) := by
  have hp : Rated (fun x => GeneralPaperTreeEpochPreparation.profile (GeneralPaperFastRationalMajorant.model C d)
      (W x) x.m x.k x.Qv (alphabet x)) 1 2 1 := (preparationCertificate C d W hW).bound
  have hf : Rated (fun x => GeneralPaperForestUpdatePrice.profile (GeneralPaperFastRationalMajorant.model C d).rat
      (W x) x.m (alphabet x).lambda x.k x.Qv) 1 2 1 := (forestCertificate C d W hW).bound
  have hi : Rated (fun x => GeneralPaperEpochInitialFamilyPrice.profile (GeneralPaperFastRationalMajorant.model C d).rat
      (W x) x.m x.k) 1 0 1 := (localInitialCertificate C d W hW).bound
  have ha : Rated (fun x => GeneralPaperTrajectoryAppendPrice.profile (W x)
      (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows
      (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).period) 0 0 1 :=
    (appendCertificate C d W hW).bound
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hpc : Rated (fun x => arrayWord (W x)
      ((GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).period+2)) 0 0 0 :=
    poly (array_poly W _ hW (by fun_prop))
  have hec : Rated (fun x => arrayWord (W x)
      ((GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs+2)) 0 0 0 :=
    poly (array_poly W _ hW (by fun_prop))
  refine ⟨_,_,_,by
    dsimp only [background]
    fun_prop⟩

theorem background_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((backgroundCertificate C d W hW).fields,(backgroundCertificate C d W hW).symbols,
      (backgroundCertificate C d W hW).accuracy)=(1,2,1) := rfl

theorem epoch_rate : Rated (fun x => (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs) 0 1 1 := by
  apply bounded (2^37)
  intro x
  have he := (GeneralPaperTrajectoryParameters.epochs_upper (alphabet x).lambda x.k).le
  have hs : (alphabet x).lambda+2≤2*symbols x := by unfold symbols; omega
  have h := he.trans (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right (2^(35+x.k)) hs))
  apply h.trans_eq
  simp only [monomial,pow_zero,pow_one,Nat.one_mul,accuracy,pow_add]
  norm_num only [show (2:ℕ)^35=34359738368 by decide,show (2:ℕ)^37=137438953472 by decide]
  ring

theorem rows_rate : Rated (fun x => (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows) 0 1 2 := by
  simpa only [Rated,Soft,monomial,pow_zero,pow_one,Nat.one_mul] using GeneralPaperSharpSourceDPContract.rows_rate

def sourceRate (x : Input) : ℕ := monomial 1 3 2 x+monomial 1 2 4 x

theorem full_profile_soft (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    Soft sourceRate (fun x => GeneralPaperFastSourceMajorant.profile C d (W x) x.m x.k x.Qv (alphabet x)
      (GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs) := by
  have hi : Rated (fun x => GeneralPaperGeometricSourcePrice.initialProfile (W x) x.m (alphabet x).lambda x.k) 1 0 0 :=
    (initialCertificate C d W hW).bound
  have hb : Rated (fun x => background C d (W x) x.m x.k x.Qv (alphabet x)) 1 2 1 :=
    (backgroundCertificate C d W hW).bound
  have hr : Rated (fun x => GeneralPaperSelectorRefinedSourcePrice.roundProfile (GeneralPaperFastRationalMajorant.model C d)
      C d (W x) x.m (alphabet x).lambda x.k x.Qv) 1 1 2 := (roundCertificate C d W hW).bound
  have hfirst := add_same (weaken hi (by decide : 1≤1) (by decide : 0≤3) (by decide : 0≤2))
    (GeneralPaperSourceRateAlgebra.mul _ _ 0 1 1 1 2 1 epoch_rate hb)
  have hsecond := GeneralPaperSourceRateAlgebra.mul _ _ 0 1 2 1 1 2 rows_rate hr
  have hall := GeneralPaperSourceSoftBounds.add hfirst hsecond
  apply dominated hall
  intro x
  dsimp only [GeneralPaperFastSourceMajorant.profile,GeneralPaperSelectorRefinedSourcePrice.profile]
  rw [step_split,GeneralPaperTrajectoryParameters.rows_product]
  exact le_of_eq (by ring)

theorem profile_prefix_mono (C d W m k Qv : ℕ) (a : Alphabet) {count limit : ℕ} (h : count≤limit) :
    GeneralPaperFastSourceMajorant.profile C d W m k Qv a count≤
      GeneralPaperFastSourceMajorant.profile C d W m k Qv a limit := by
  unfold GeneralPaperFastSourceMajorant.profile GeneralPaperSelectorRefinedSourcePrice.profile
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem prefix_profile_bound (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ∃ A e : ℕ,∀ (x : Input) (count : ℕ),
      count≤(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs →
      GeneralPaperFastSourceMajorant.profile C d (W x) x.m x.k x.Qv (alphabet x) count≤
        A*sourceRate x*(logSize x)^e := by
  rcases full_profile_soft C d W hW with ⟨A,e,hA⟩
  exact ⟨A,e,fun x count he => (profile_prefix_mono C d (W x) x.m x.k x.Qv (alphabet x) he).trans (hA x)⟩

theorem common_word_prefix_bound (C d : ℕ) :
    ∃ A e : ℕ,∀ (x : Input) (count : ℕ),
      count≤(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs →
      GeneralPaperFastSourceMajorant.profile C d (GeneralPaperLogarithmicSourceReference.width C d x)
        x.m x.k x.Qv (alphabet x) count≤A*sourceRate x*(logSize x)^e :=
  prefix_profile_bound C d _ (GeneralPaperLogarithmicSourceReference.width_tight C d)

def paperRate (x : Input) : ℕ :=
  x.m*(alphabet x).lambda^3*2^(2*x.k)+x.m*(alphabet x).lambda^2*2^(4*x.k)

theorem nonempty_rate (x : Input) (hm : 1≤x.m) : sourceRate x≤16*paperRate x := by
  have hl := GeneralPaperSourceAlphabetLower.fields_le_lambda x.m x.k
  change x.m≤(alphabet x).lambda at hl
  have hm' : fields x≤2*x.m := by unfold fields; omega
  have hl' : symbols x≤2*(alphabet x).lambda := by unfold symbols; omega
  have h1 := Nat.mul_le_mul_right ((accuracy x)^2) (Nat.mul_le_mul hm' (Nat.pow_le_pow_left hl' 3))
  have h2 := Nat.mul_le_mul_right ((accuracy x)^4) (Nat.mul_le_mul hm' (Nat.pow_le_pow_left hl' 2))
  have hp := Nat.add_le_add h1 h2
  have he : (2*x.m)*(2*(alphabet x).lambda)^3*(accuracy x)^2+
      (2*x.m)*(2*(alphabet x).lambda)^2*(accuracy x)^4=
      16*(x.m*(alphabet x).lambda^3*(accuracy x)^2)+8*(x.m*(alphabet x).lambda^2*(accuracy x)^4) := by ring
  have hb : 16*(x.m*(alphabet x).lambda^3*(accuracy x)^2)+8*(x.m*(alphabet x).lambda^2*(accuracy x)^4)≤
      16*(x.m*(alphabet x).lambda^3*(accuracy x)^2+x.m*(alphabet x).lambda^2*(accuracy x)^4) := by
    nlinarith only [Nat.zero_le (x.m*(alphabet x).lambda^2*(accuracy x)^4)]
  apply (show sourceRate x≤_ by simpa only [sourceRate,monomial,pow_one] using hp).trans
  rw [he]
  apply hb.trans_eq
  simp only [paperRate,accuracy,←pow_mul,Nat.mul_comm x.k 2,Nat.mul_comm x.k 4]

theorem paper_prefix_bound (C d : ℕ) :
    ∃ A e : ℕ,∀ (x : Input) (count : ℕ),1≤x.m →
      count≤(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).epochs →
      GeneralPaperFastSourceMajorant.profile C d (GeneralPaperLogarithmicSourceReference.width C d x)
        x.m x.k x.Qv (alphabet x) count≤A*paperRate x*(logSize x)^e := by
  rcases common_word_prefix_bound C d with ⟨A,e,hA⟩
  refine ⟨16*A,e,?_⟩
  intro x count hm he
  apply (hA x count he).trans
  exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left A (nonempty_rate x hm))).trans_eq (by ring)

end Blotto.GeneralPaperSharpSourceBitRate
