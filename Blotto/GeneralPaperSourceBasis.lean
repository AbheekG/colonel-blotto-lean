import Blotto.GeneralPaperBasisFull

/-! The actual full geometric source, actual strict-score preparation and
native common-grid initializer feed the actual full basis controller.
Every precondition is derived from the source's own returned data.
-/
namespace Blotto.GeneralPaperSourceBasis
open RationalOrderCell GeneralPaperSourceInitializer GeneralPaperInitializerSelectedControls
open GeneralPaperProxyParameters GeneralPaperBasisGridInputs GeneralPaperBasisInvariant
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

noncomputable def initialCoordinates {m : ℕ} (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (reciprocal : Bool) :
    Variable m (prepare m k).K → ℚ :=
  let init := initial k Qv hQv weights hp hs b reciprocal
  fun a => init.anchor a.1 (GeneralPaperTransferPolytopePoint.positiveLabel a.2)

def fromPrepared {T m : ℕ} (k : ℕ)
    (prep : GeneralPaperTransferPreparation.Prepared T m (prepare m k).K (prepare m k).S)
    (v : RationalFieldSelector m) (p q : ℕ) (reciprocal : Bool) :=
  let c := GeneralPaperInitializerParameters.prepare m (prepare m k).H p q reciprocal
  let init := GeneralPaperInitializerDictionary.build prep.dictionary c.N c.depth
  let initialPoint := fun a : Variable m (prepare m k).K =>
    init.anchor a.1 (GeneralPaperTransferPolytopePoint.positiveLabel a.2)
  GeneralPaperBasisFromGrid.run (GeneralPaperScoreScaleParameters.prepare m k).depth prep.dictionary
    v (prepare m k).S prep.threshold (prepare m k).H p q reciprocal initialPoint

noncomputable def run {m : ℕ} (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (reciprocal : Bool) :=
  let prep := prepared k Qv hQv weights hp hs b reciprocal
  let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
  fromPrepared k prep (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) f.num f.den reciprocal

theorem run_valid {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    let prep := prepared k Qv hQv weights hp hs b reciprocal
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    ∃ state,run k Qv hQv weights hp hs b reciprocal=some state ∧
      Invariant prep.dictionary (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs) (prepare m k).S prep.threshold
        (controls m k b reciprocal).N (auxiliaryNumerator m (prepare m k).H f.num f.den reciprocal)
        (grid (controls m k b reciprocal).N (initialCoordinates k Qv hQv weights hp hs b reciprocal)) (Nat.le_refl _) state := by
  have hSource := sound k Qv hm hQv weights hp hs b hb reciprocal
  have hf := GeneralPaperProxyClassifier.proxy_integer_representation m k b hb
  have hGrid (a : Variable m (prepare m k).K) : OnRationalLattice (controls m k b reciprocal).N
      (initialCoordinates k Qv hQv weights hp hs b reciprocal a) := hSource.2.2 a.1 _
  exact GeneralPaperBasisFromGrid.run_valid (GeneralPaperScoreScaleParameters.prepare m k).depth
    (prepared k Qv hQv weights hp hs b reciprocal).dictionary (GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs)
    (GeneralPaperScoreScaleParameters.labels_positive m k) (prepare m k).S _ (prepare m k).H
    _ _ (GeneralPaperScoreScaleParameters.score_cap m k) reciprocal hm (H_positive m k) hf.1 (by omega)
    (initialCoordinates k Qv hQv weights hp hs b reciprocal) hGrid hSource.2.1

end Blotto.GeneralPaperSourceBasis
