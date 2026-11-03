import Blotto.GeneralPaperSourcePairCases

/-! The actual classified full-source pair always returns. Its decoded
canonical whole-row laws satisfy hard unit budgets and the paper paired
security bound with exactly one m/S transfer loss. No supplied source or
endpoint security premise remains.
-/
namespace Blotto.GeneralPaperSourcePairSound
open GeneralPaperProxyParameters GeneralPaperDictionary GeneralPaperSourcePairRun GeneralPaperSourcePairContract
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

theorem run_contract {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) :
    ∃ pair,run k Qv hQv weights hp hs b=some pair ∧ Contract k Qv hQv weights hp hs b pair := by
  cases he : (GeneralPaperProxyClassifier.classify m k b).choice.modify with
  | none => exact GeneralPaperSourcePairCases.unchanged k Qv hm hQv weights hp hs b hb he
  | some side =>
    cases side with
    | rich => exact GeneralPaperSourcePairCases.rich k Qv hm hQv weights hp hs b hb he
    | poor => exact GeneralPaperSourcePairCases.poor k Qv hm hQv weights hp hs b hb he

theorem paired_security {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) :
    ∃ pair,run k Qv hQv weights hp hs b=some pair ∧ Contract k Qv hQv weights hp hs b pair ∧
      security (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs).values b
        (law pair.rich (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)).law+
      security (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs).values (1/b)
        (law pair.poor (GeneralPaperTrajectoryParameters.rows_positive (alphabet m k).lambda k)).law≤
        1+3*((GeneralPaperSourceParameters.prepare k).z:ℝ)/32+2/((prepare m k).K:ℝ)+(m:ℝ)/(prepare m k).S := by
  obtain ⟨pair,hRun,hc⟩ := run_contract k Qv hm hQv weights hp hs b hb
  have hSource := GeneralPaperSourceRawPairSecurity.bound k Qv hm hQv weights hp hs b hb
  exact ⟨pair,hRun,hc,by linarith only [hc.security_bound,hSource]⟩

end Blotto.GeneralPaperSourcePairSound
