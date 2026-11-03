import Blotto.GeneralPaperSourcePairSound

/-! Restore the actual real poor budget b, preserving every tie and hard
budget. The independent whole-player laws have continuous-deviation Nash
regrets bounded by the actual paired security gap. Circle lifting, value
reduction and complete paper computation/output prices remain separate.
-/
namespace Blotto.GeneralPaperSourcePairCanonical
open GeneralPaperDictionary GeneralPaperSourcePairRun GeneralPaperProxyParameters
open GeneralPaperTransferPreparation
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

noncomputable def richLaw {T m K : ℕ} (pair : Pair T m K) (hT : 0<T) : Mixed m := (law pair.rich hT).law

noncomputable def poorLaw {T m K : ℕ} (pair : Pair T m K) (hT : 0<T) (b : ℝ) : Mixed m := scaleLaw b (law pair.poor hT).law

theorem poor_rows {T m K : ℕ} (pair : Pair T m K) (hT : 0<T) (hK : 0<K)
    (hu : UnitDictionary pair.poor hT hK) (b : ℝ) (hb : 0≤b) (i : Fin T) :
    Blotto.Feasible b (scaleAllocation b ((law pair.poor hT).realRow i)) := by
  have hh := scaleAllocation_feasible hb (hu.feasible i)
  simpa only [mul_one] using hh

theorem canonical {T m K : ℕ} (pair : Pair T m K) (hT : 0<T) (hK : 0<K)
    (huA : UnitDictionary pair.rich hT hK) (huB : UnitDictionary pair.poor hT hK)
    (v : Values m) (b : ℝ) (hb : 0<b) (error : ℝ)
    (hSec : security v b (law pair.rich hT).law+security v (1/b) (law pair.poor hT).law≤1+error) :
    Supported 1 (richLaw pair hT) ∧ Supported b (poorLaw pair hT b) ∧
      regret v 1 (richLaw pair hT) (poorLaw pair hT b)≤error ∧
        regret v b (poorLaw pair hT b) (richLaw pair hT)≤error := by
  have hB := scaleLaw_supported hb.le (law pair.poor hT).law huB.supported
  have hB' : Supported b (poorLaw pair hT b) := by simpa only [poorLaw,mul_one] using hB
  have hScale := security_scale v hb (1/b) (law pair.poor hT).law
  have he : b*(1/b)=1 := by field_simp
  rw [he] at hScale
  have hActual : security v 1 (poorLaw pair hT b)+security v b (richLaw pair hT)≤1+error := by
    unfold richLaw poorLaw
    rw [hScale]
    linarith only [hSec]
  have hRegrets := regrets_le_of_security_sum v (richLaw pair hT) (poorLaw pair hT b) huA.supported hB' hActual
  exact ⟨huA.supported,hB',hRegrets⟩

theorem run_regrets {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) :
    ∃ pair,run k Qv hQv weights hp hs b=some pair ∧ GeneralPaperSourcePairContract.Contract k Qv hQv weights hp hs b pair ∧
      Supported 1 (richLaw pair (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)) ∧
      Supported b (poorLaw pair (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) b) ∧
      regret (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs).values 1
        (richLaw pair (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k))
        (poorLaw pair (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) b)≤
          3*((GeneralPaperSourceParameters.prepare k).z:ℝ)/32+2/((prepare m k).K:ℝ)+(m:ℝ)/(prepare m k).S ∧
      regret (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs).values b
        (poorLaw pair (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k) b)
        (richLaw pair (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k))≤
          3*((GeneralPaperSourceParameters.prepare k).z:ℝ)/32+2/((prepare m k).K:ℝ)+(m:ℝ)/(prepare m k).S := by
  obtain ⟨pair,hRun,hc,hSec⟩ := GeneralPaperSourcePairSound.paired_security k Qv hm hQv weights hp hs b hb
  have hSec' : security (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs).values b
      (law pair.rich (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)).law+
      security (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs).values (1/b)
      (law pair.poor (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)).law≤
      1+(3*((GeneralPaperSourceParameters.prepare k).z:ℝ)/32+2/((prepare m k).K:ℝ)+(m:ℝ)/(prepare m k).S) := by
    linarith only [hSec]
  exact ⟨pair,hRun,hc,canonical pair _ _ hc.rich_unit hc.poor_unit _ b hb.1 _ hSec'⟩

end Blotto.GeneralPaperSourcePairCanonical
