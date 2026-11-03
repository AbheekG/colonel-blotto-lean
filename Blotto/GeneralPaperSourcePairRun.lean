import Blotto.GeneralPaperSourceRawPairSecurity

/-! Actual original-ratio pair construction. Only the defender selected
by the classifier calls the strict-score/basis endpoint compiler; unchanged
defenders only decode, quantize and normalize their own full source rows.
-/
namespace Blotto.GeneralPaperSourcePairRun
open GeneralPaperProxyParameters GeneralPaperDictionary
open scoped BigOperators
set_option autoImplicit false

structure Pair (T m K : ℕ) where
  rich : Dictionary T m K
  poor : Dictionary T m K

noncomputable def run {m : ℕ} (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) :
    Option (Pair (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows m (prepare m k).K) :=
  match (GeneralPaperProxyClassifier.classify m k b).choice.modify with
  | none => some ⟨GeneralPaperSourceUnchangedDictionary.run k Qv weights b false,
      GeneralPaperSourceUnchangedDictionary.run k Qv weights b true⟩
  | some .rich => (GeneralPaperSourceModifiedDictionary.run k Qv hQv weights hp hs b false).map
      (fun d => ⟨d,GeneralPaperSourceUnchangedDictionary.run k Qv weights b true⟩)
  | some .poor => (GeneralPaperSourceModifiedDictionary.run k Qv hQv weights hp hs b true).map
      (fun d => ⟨GeneralPaperSourceUnchangedDictionary.run k Qv weights b false,d⟩)

end Blotto.GeneralPaperSourcePairRun
