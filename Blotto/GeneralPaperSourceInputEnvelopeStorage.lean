import Blotto.GeneralPaperSourceUnitCallerReachedRates

/-! Exact data-footprint abstraction of the closed prepared/source
storage profile. Its retained input-footprint and two budget-word leaves are abstracted.
Actual weights, budgets, native data and execution are unchanged; this
numeric envelope is erased and has no artificial replacement inputs. -/
namespace Blotto.GeneralPaperSourceInputEnvelopeStorage
open GeneralPaperEncodedScalarStorage GeneralPaperCodeAlphabet
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

noncomputable def profile (model : RationalCostModel) (W m k Qv t : ℕ) (a : Alphabet) (F U V : ℕ) : ℕ :=
  (Blotto.GeneralPaperPrecallResidentStorage.inputProfile W m k Qv 0 t t +
              (Blotto.GeneralPaperClassifierResultStorage.frontProfile W m k +
                  ((Blotto.GeneralPaperMaterializedCacheStorage.gridProfile W m a.lambda k Qv +
                      have H := Blotto.GeneralPaperPowerPreparationEnvelope.operandWidth m a.lambda k Qv;
                      Blotto.GeneralPaperEncodedPreparedPowers.profile W m a.lambda k Qv +
                                  Blotto.GeneralPaperEncodedSharedParameters.preparedProfitProfile W m a.lambda k Qv +
                                5 * (H + W) +
                              H +
                            2 * Blotto.GeneralPaperSharedSpanPrice.width a +
                          F +
                        160 * W) +
                    Blotto.GeneralPaperEpochResidentStorage.profile W m a.lambda k Qv) +
                64 * W) +
            Blotto.GeneralPaperEncodedTrajectoryStorage.profile W m a.lambda k +
          have E := (Blotto.GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs;
          Blotto.GeneralPaperEncodedForestStorage.profile W m a.lambda k Qv +
                  E * Blotto.GeneralPaperTrajectoryControllerStorage.frameProfile W E +
                Max.max (Blotto.GeneralPaperSourceLifetimeStorage.baseProfile W m a.lambda k)
                  (Blotto.GeneralPaperSourceLifetimeStorage.returnedProfile W m a.lambda k Qv +
                        Max.max
                          ((have H := Blotto.GeneralPaperPowerPreparationEnvelope.operandWidth m a.lambda k Qv;
                                    Blotto.GeneralPaperEncodedPreparedPowers.profile W m a.lambda k Qv +
                                                Blotto.GeneralPaperEncodedSharedParameters.preparedProfitProfile W m
                                                  a.lambda k Qv +
                                              5 * (H + W) +
                                            H +
                                          2 * Blotto.GeneralPaperSharedSpanPrice.width a +
                                        F +
                                      160 * W) +
                                    Blotto.GeneralPaperEpochResidentStorage.profile W m a.lambda k Qv +
                                  Blotto.GeneralPaperActualEpochParentStorage.profile model W m k Qv a +
                                Max.max (Blotto.GeneralPaperEpochSourcePhaseStorage.childrenProfile model W m k a)
                                  (have P := (Blotto.GeneralPaperTrajectoryParameters.prepare a.lambda k).period;
                                  Blotto.GeneralPaperEncodedEpochLevels.profile W m a.lambda k Qv +
                                          P * Blotto.GeneralPaperTrajectoryControllerStorage.frameProfile W P +
                                        Max.max
                                          (Blotto.GeneralPaperLocalSourceLifetimeStorage.baseProfile model W m a.lambda
                                            k Qv)
                                          (Max.max
                                                    (Blotto.GeneralPaperSnapshotFamilyConstructionStorage.profile model
                                                      W m a.lambda k Qv)
                                                    (Max.max
                                                      (have p :=
                                                        Blotto.GeneralPaperProfitParameters.prepare m a.lambda k Qv;
                                                      (have prepared :=
                                                          Blotto.GeneralPaperProfitParameters.prepare m a.lambda k Qv;
                                                        (have H :=
                                                                Blotto.GeneralPaperPowerPreparationEnvelope.operandWidth
                                                                  m a.lambda k Qv;
                                                              Blotto.GeneralPaperEncodedPreparedPowers.profile W m
                                                                            a.lambda k Qv +
                                                                          Blotto.GeneralPaperEncodedSharedParameters.preparedProfitProfile
                                                                            W m a.lambda k Qv +
                                                                        5 * (H + W) +
                                                                      H +
                                                                    2 * Blotto.GeneralPaperSharedSpanPrice.width a +
                                                                  F +
                                                                160 * W) +
                                                              Blotto.GeneralPaperEpochResidentStorage.profile W m
                                                                a.lambda k Qv +
                                                            2 *
                                                              Blotto.GeneralPaperActualProfitTreeStorage.profile W m
                                                                a.lambda k Qv prepared +
                                                          2 *
                                                            Blotto.GeneralPaperNativeSelectorOutputStorage.profile W m
                                                              ((Blotto.GeneralPaperSourceParameters.prepare
                                                                    k).summarySize +
                                                                2)
                                                              prepared.grid.size prepared.parameters.height) +
                                                        2 *
                                                          Blotto.GeneralPaperDPConstructionStorage.profile W
                                                            ((Blotto.GeneralPaperSourceParameters.prepare
                                                                  k).summarySize +
                                                              2)
                                                            p.grid.size (a.lambda + 1) p.parameters.height)
                                                      ((have p :=
                                                                Blotto.GeneralPaperProfitParameters.prepare m a.lambda k
                                                                  Qv;
                                                              (have p :=
                                                                    Blotto.GeneralPaperProfitParameters.prepare m
                                                                      a.lambda k Qv;
                                                                  (have prepared :=
                                                                      Blotto.GeneralPaperProfitParameters.prepare m
                                                                        a.lambda k Qv;
                                                                    (have H :=
                                                                            Blotto.GeneralPaperPowerPreparationEnvelope.operandWidth
                                                                              m a.lambda k Qv;
                                                                          Blotto.GeneralPaperEncodedPreparedPowers.profile
                                                                                        W m a.lambda k Qv +
                                                                                      Blotto.GeneralPaperEncodedSharedParameters.preparedProfitProfile
                                                                                        W m a.lambda k Qv +
                                                                                    5 * (H + W) +
                                                                                  H +
                                                                                2 *
                                                                                  Blotto.GeneralPaperSharedSpanPrice.width
                                                                                    a +
                                                                              F +
                                                                            160 * W) +
                                                                          Blotto.GeneralPaperEpochResidentStorage.profile
                                                                            W m a.lambda k Qv +
                                                                        2 *
                                                                          Blotto.GeneralPaperActualProfitTreeStorage.profile
                                                                            W m a.lambda k Qv prepared +
                                                                      2 *
                                                                        Blotto.GeneralPaperNativeSelectorOutputStorage.profile
                                                                          W m
                                                                          ((Blotto.GeneralPaperSourceParameters.prepare
                                                                                k).summarySize +
                                                                            2)
                                                                          prepared.grid.size
                                                                          prepared.parameters.height) +
                                                                    2 *
                                                                      Blotto.GeneralPaperDPConstructionStorage.profile W
                                                                        ((Blotto.GeneralPaperSourceParameters.prepare
                                                                              k).summarySize +
                                                                          2)
                                                                        p.grid.size (a.lambda + 1)
                                                                        p.parameters.height) +
                                                                  Blotto.GeneralPaperRootProfitPhaseStorage.profile W m
                                                                    a.lambda k Qv p (U) +
                                                                Blotto.GeneralPaperRootProfitPhaseStorage.profile W m
                                                                  a.lambda k Qv p (V)) +
                                                              2 *
                                                                Blotto.GeneralPaperNativeProfitLeafStorage.elementProfile
                                                                  model W m a.lambda k Qv +
                                                            Blotto.GeneralPaperSourceGridCallbackStorage.gridProfile
                                                              model W m a.lambda k Qv +
                                                          Blotto.GeneralPaperActualUpdateConstructionStorage.roundProfile
                                                            model W m a.lambda k Qv +
                                                        2 *
                                                          Blotto.GeneralPaperSelectedRowConstructionStorage.profile W m
                                                            a.lambda k)) +
                                                  256 * W +
                                                Blotto.GeneralPaperLocalSourceLifetimeStorage.returnedProfile W m
                                                  a.lambda k Qv +
                                              256 *
                                                Blotto.GeneralPaperSummaryArrayExecution.arrayWord W
                                                  ((Blotto.GeneralPaperTrajectoryParameters.prepare a.lambda k).period +
                                                    2) +
                                            256 * W) +
                                      Blotto.GeneralPaperLocalSourceLifetimeStorage.returnedProfile W m a.lambda k Qv +
                                    128 * W) +
                              Blotto.GeneralPaperEpochSourcePhaseStorage.returnedProfile W m a.lambda k Qv +
                            256 * W)
                          (Blotto.GeneralPaperSourceLifetimeStorage.appendProfile W m a.lambda k +
                            Blotto.GeneralPaperSourceLifetimeStorage.returnedProfile W m a.lambda k Qv) +
                      131 *
                        Blotto.GeneralPaperSummaryArrayExecution.arrayWord W
                          ((Blotto.GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs + 2) +
                    256 * W) +
              Blotto.GeneralPaperSourceLifetimeStorage.returnedProfile W m a.lambda k Qv +
            128 * W) +
        Blotto.GeneralPaperClassifierConstructionStorage.profile model W m k 0 +
      Blotto.GeneralPaperPreparationResidentStorage.constructionProfile model W m a.lambda k Qv

theorem profile_eq {m : ℕ} (model : RationalCostModel) (W k Qv t : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    GeneralPaperPreparedReferenceCapacity.profile model W k Qv 0 t t a weights Bc Br=
      profile model W m k Qv t a (GeneralPaperEncodedSharedSource.inputFootprint W weights Bc Br) (rationalWordWidth Bc) (rationalWordWidth Br) := by
  unfold profile GeneralPaperPreparedReferenceCapacity.profile GeneralPaperPrecallResidentStorage.residentProfile GeneralPaperSourceLifetimeStorage.profile
    GeneralPaperPreparationResidentStorage.residentProfile GeneralPaperSourceLifetimeStorage.phaseProfile GeneralPaperEpochSourcePhaseStorage.profile
    GeneralPaperLocalSourceLifetimeStorage.profile GeneralPaperLocalSourceLifetimeStorage.phaseProfile GeneralPaperRoundPhaseStorage.profile
    GeneralPaperSelectedRowConstructionStorage.sourceProfile GeneralPaperSourceUpdateConstructionStorage.profile GeneralPaperSourceGridCallbackStorage.profile
    GeneralPaperActualQueryCallbackStorage.profile GeneralPaperActualRootProfitStorage.profile GeneralPaperActualDPConstructionStorage.profile
    GeneralPaperSelectorResidentStorage.profile GeneralPaperEncodedSharedSource.profile
  rfl

theorem profile_mono (model : RationalCostModel) (W m k Qv t : ℕ) (a : Alphabet)
    (F G U V u v : ℕ) (h : F≤G) (hu : U≤u) (hv : V≤v) :
    profile model W m k Qv t a F U V≤profile model W m k Qv t a G u v := by
  unfold profile GeneralPaperRootProfitPhaseStorage.profile GeneralPaperRootSelectionStorage.profile
  dsimp only
  gcongr

theorem prepared_bound {m : ℕ} (model : RationalCostModel) (W k Qv t F U V : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hF : GeneralPaperEncodedSharedSource.inputFootprint W weights Bc Br≤F)
    (hc : rationalWordWidth Bc≤U) (hr : rationalWordWidth Br≤V) :
    GeneralPaperPreparedReferenceCapacity.profile model W k Qv 0 t t a weights Bc Br≤profile model W m k Qv t a F U V := by
  rw [profile_eq]
  exact profile_mono model W m k Qv t a _ _ _ _ _ _ hF hc hr

theorem lifetime_bound {m : ℕ} (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n)
    (W k Qv t F U V : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (hF : GeneralPaperEncodedSharedSource.inputFootprint W weights Bc Br≤F)
    (hc : rationalWordWidth Bc≤U) (hr : rationalWordWidth Br≤V) :
    GeneralPaperSourceLifetimeStorage.profile actual W k Qv a weights Bc Br≤profile upper W m k Qv t a F U V := by
  have hFirst : GeneralPaperSourceLifetimeStorage.profile actual W k Qv a weights Bc Br≤
      GeneralPaperPreparedReferenceCapacity.profile actual W k Qv 0 t t a weights Bc Br := by
    unfold GeneralPaperPreparedReferenceCapacity.profile
    omega
  exact hFirst.trans ((GeneralPaperSourceSpaceMonotonicity.prepared actual upper h W k Qv 0 t t a weights Bc Br).trans
    (prepared_bound upper W k Qv t F U V a weights Bc Br hF hc hr))

theorem power_profile {m : ℕ} (model : RationalCostModel) (W k Qv t : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    GeneralPaperMaterializedCacheStorage.powerProfile W m a.lambda k Qv≤
      GeneralPaperPreparedReferenceCapacity.profile model W k Qv 0 t t a weights Bc Br := by
  unfold GeneralPaperPreparedReferenceCapacity.profile GeneralPaperPrecallResidentStorage.residentProfile
    GeneralPaperPreparationResidentStorage.residentProfile GeneralPaperMaterializedCacheStorage.gridProfile
  omega

theorem shared_profile {m : ℕ} (model : RationalCostModel) (W k Qv t : ℕ) (a : Alphabet)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    GeneralPaperEncodedSharedSource.profile W k Qv a weights Bc Br≤
      GeneralPaperPreparedReferenceCapacity.profile model W k Qv 0 t t a weights Bc Br := by
  unfold GeneralPaperPreparedReferenceCapacity.profile GeneralPaperPrecallResidentStorage.residentProfile
    GeneralPaperPreparationResidentStorage.residentProfile
  omega

def inputCap (W m Qv t : ℕ) : ℕ := m*(1+binaryWordWidth Qv+W)+32*W+2*(1+2*t)+64*W

theorem input_bound {m : ℕ} (W Qv t : ℕ) (weights : FixedArrayTable m ℕ) (hs : ∑ j,weights.read j=Qv)
    (Bc Br : ℚ) (hc : RationalHeight Bc t) (hr : RationalHeight Br t) :
    GeneralPaperEncodedSharedSource.inputFootprint W weights Bc Br≤ inputCap W m Qv t := by
  have hw := GeneralPaperEncodedNatArray.bounded W (1+binaryWordWidth Qv) weights
    (fun j => Nat.add_le_add_left (binaryWordWidth_mono (GeneralPaperSourceScoreHeights.weight_le Qv weights hs j)) 1)
  have hBc := rationalWordWidth_of_height hc
  have hBr := rationalWordWidth_of_height hr
  unfold GeneralPaperEncodedSharedSource.inputFootprint inputCap
  omega

/-- A numeric encoding witness used only to transfer an existing scaling theorem.
It is never passed to source preparation or execution. -/
def widthWitness (t : ℕ) : ℚ := ((2^(2*(t-1)) : ℕ) : ℚ)

theorem witness_width (t : ℕ) (ht : 1≤t) : rationalWordWidth (widthWitness t)=1+2*t := by
  simp only [widthWitness,rationalWordWidth,Rat.num_natCast,Rat.den_natCast,Int.natAbs_natCast,
    binaryWordWidth,Nat.log2_two_pow]
  change 1+(2*(t-1)+1)+1=1+2*t
  omega

theorem witness_input (W m Qv t : ℕ) (ht : 1≤t) :
    GeneralPaperEncodedSharedSource.inputFootprint W (FixedArrayTable.ofFn (fun _ : Fin m => Qv))
      (widthWitness t) (widthWitness t)=inputCap W m Qv t := by
  simp only [GeneralPaperEncodedSharedSource.inputFootprint,GeneralPaperEncodedNatArray.footprint,
    GeneralPaperEncodedNatArray.payload,FixedArrayTable.read_ofFn,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,witness_width t ht,inputCap]
  ring

theorem scaling (model : RationalCostModel) (m k Qv t : ℕ) (a : Alphabet) (ht : 1≤t) :
    GeneralPaperReferenceScaling.Scale (fun W => profile model W m k Qv t a
      (inputCap W m Qv t) (1+2*t) (1+2*t)) := by
  simpa only [profile_eq,witness_input _ m Qv t ht,witness_width t ht] using
    (GeneralPaperPreparedReferenceCapacity.scaling model k Qv 0 t t a
      (FixedArrayTable.ofFn (fun _ : Fin m => Qv)) (widthWitness t) (widthWitness t))

theorem input_scaling (m Qv t : ℕ) : GeneralPaperReferenceScaling.Scale (fun W => inputCap W m Qv t) := by
  unfold inputCap
  fun_prop

end Blotto.GeneralPaperSourceInputEnvelopeStorage
