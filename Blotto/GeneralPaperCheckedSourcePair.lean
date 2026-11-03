import Blotto.GeneralPaperCheckedEndpointBranch
import Blotto.GeneralPaperSourceDyadicEquilibrium

/-! The actual pair with the prescribed endpoint rechecks. Unchanged
defenders skip unused strict-score calls. Every valid classifier case
returns the same literal dictionaries as the established mathematical core.
-/
namespace Blotto.GeneralPaperCheckedSourcePair
open GeneralPaperProxyParameters GeneralPaperSourcePairRun
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

noncomputable def modified {m : ℕ} (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (reciprocal : Bool) :=
  (GeneralPaperCheckedEndpointBranch.run k Qv hQv weights hp hs b reciprocal).map GeneralPaperEndpointDictionary.dictionary

noncomputable def run {m : ℕ} (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) :
    Option (Pair (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K) :=
  match (GeneralPaperProxyClassifier.classify m k b).choice.modify with
  | none => some ⟨GeneralPaperSourceUnchangedDictionary.run k Qv weights b false,
      GeneralPaperSourceUnchangedDictionary.run k Qv weights b true⟩
  | some .rich => (modified k Qv hQv weights hp hs b false).map
      (fun d => ⟨d,GeneralPaperSourceUnchangedDictionary.run k Qv weights b true⟩)
  | some .poor => (modified k Qv hQv weights hp hs b true).map
      (fun d => ⟨GeneralPaperSourceUnchangedDictionary.run k Qv weights b false,d⟩)

theorem run_eq {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) :
    run k Qv hQv weights hp hs b=GeneralPaperSourcePairRun.run k Qv hQv weights hp hs b := by
  cases he : (GeneralPaperProxyClassifier.classify m k b).choice.modify with
  | none => simp only [run,GeneralPaperSourcePairRun.run,he]
  | some side =>
    cases side with
    | rich => simp only [run,GeneralPaperSourcePairRun.run,he,modified,GeneralPaperSourceModifiedDictionary.run,
        GeneralPaperCheckedEndpointBranch.rich_eq k Qv hm hQv weights hp hs b hb he]
    | poor => simp only [run,GeneralPaperSourcePairRun.run,he,modified,GeneralPaperSourceModifiedDictionary.run,
        GeneralPaperCheckedEndpointBranch.poor_eq k Qv hm hQv weights hp hs b hb he]

theorem run_contract {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) :
    ∃ pair,run k Qv hQv weights hp hs b=some pair ∧ GeneralPaperSourcePairContract.Contract k Qv hQv weights hp hs b pair := by
  rw [run_eq k Qv hm hQv weights hp hs b hb]
  exact GeneralPaperSourcePairSound.run_contract k Qv hm hQv weights hp hs b hb

end Blotto.GeneralPaperCheckedSourcePair
