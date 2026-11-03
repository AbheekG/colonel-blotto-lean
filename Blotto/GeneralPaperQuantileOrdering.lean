import Blotto.GeneralPaperQuantileOrderCompare

/-! The actual quantile output is nondecreasing in target order. Each node
of the deterministic descent compares against a fixed stored prefix; the
sequence of approximate masses need not be monotone across different nodes.
-/
namespace Blotto.GeneralPaperQuantileOrdering
open GeneralPaperDyadicFloat GeneralPaperPreparedPowers GeneralPaperMassApproximation
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperGlobalNodeQuery
open GeneralPaperQuantileDescent GeneralPaperQuantilePath GeneralPaperQuantileComparison
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem run_ordered (lambda k : ℕ) (total : Number)
    (hTotal : Normal (prepare lambda k).format.unit total)
    (height : ℕ) (node : Node height) (ancestor : ℕ) (storedMass storedPrefix : Number)
    (hHeight : height≤lambda+1) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor node)
    (hMass : Bound (prepare lambda k).format.unit (queryExponent lambda k) (trueMass k ancestor node) storedMass)
    (hPrefix : Normal (prepare lambda k).format.unit storedPrefix)
    (small large : ℕ) (hOrder : small≤large) (hLarge : large≤(GeneralPaperSourceParameters.prepare k).summarySize) :
    code (run (prepare lambda k) (width lambda k) small (GeneralPaperSourceParameters.prepare k).summarySize
      total height node ancestor storedMass storedPrefix)≤
    code (run (prepare lambda k) (width lambda k) large (GeneralPaperSourceParameters.prepare k).summarySize
      total height node ancestor storedMass storedPrefix) := by
  induction height generalizing ancestor storedMass storedPrefix small large with
  | zero => exact le_refl _
  | succ height ih =>
    let left := leftMass (prepare lambda k) ancestor node storedMass
    let through := GeneralPaperDyadicAddition.add (prepare lambda k).format.unit
      (prepare lambda k).format.fractionalBits storedPrefix left.number
    have hLeft := GeneralPaperQuantileChildMass.left_bound lambda k ancestor node storedMass hHeight hValid hPath hMass
    have hRight := GeneralPaperQuantileChildMass.right_bound lambda k ancestor node storedMass hHeight hValid hPath hMass
    have hThrough : Normal (prepare lambda k).format.unit through.number :=
      GeneralPaperDyadicAddition.add_normal _ _ (GeneralPaperPowerPrecision.unit_positive lambda k)
        (GeneralPaperPowerPrecision.unit_power lambda k) storedPrefix left.number hPrefix hLeft.1
    have hChildren := child_validity lambda k node hValid
    have hPaths := child_paths _ ancestor node hPath
    have hAnti := GeneralPaperQuantileOrderCompare.choose_antitone lambda k small large total through.number
      hOrder hLarge hTotal hThrough
    by_cases hSmall : (choose lambda k small total through.number).answer=true
    · by_cases hBig : (choose lambda k large total through.number).answer=true
      · have hi := ih (leftChild node) (ancestor+offset node) left.number storedPrefix (by omega)
          hChildren.1 hPaths.1 hLeft hPrefix small large hOrder hLarge
        dsimp only [left,through,choose] at hSmall hBig hi
        simpa only [code,encode_index,run,hSmall,hBig,ite_true,left_index] using hi
      · have hBound := code_bound (prepare lambda k) (width lambda k) small
          (GeneralPaperSourceParameters.prepare k).summarySize total height (leftChild node)
          (ancestor+offset node) left.number storedPrefix
        have hLen := path_length (prepare lambda k) (width lambda k) large
          (GeneralPaperSourceParameters.prepare k).summarySize total height (rightChild node)
          (ancestor+offset node) (rightMass (prepare lambda k) ancestor node storedMass).number through.number
        dsimp only [left,through,choose] at hSmall hBig hBound hLen
        simp only [code,encode_index,run,hSmall,hBig,Bool.false_eq_true,ite_true,ite_false,left_index,right_index,hLen]
        rw [code,encode_index] at hBound
        omega
    · by_cases hBig : (choose lambda k large total through.number).answer=true
      · exact False.elim (hSmall (hAnti hBig))
      · have hi := ih (rightChild node) (ancestor+offset node)
          (rightMass (prepare lambda k) ancestor node storedMass).number through.number (by omega)
          hChildren.2 hPaths.2 hRight hThrough small large hOrder hLarge
        have hLenSmall := path_length (prepare lambda k) (width lambda k) small
          (GeneralPaperSourceParameters.prepare k).summarySize total height (rightChild node)
          (ancestor+offset node) (rightMass (prepare lambda k) ancestor node storedMass).number through.number
        have hLenLarge := path_length (prepare lambda k) (width lambda k) large
          (GeneralPaperSourceParameters.prepare k).summarySize total height (rightChild node)
          (ancestor+offset node) (rightMass (prepare lambda k) ancestor node storedMass).number through.number
        dsimp only [left,through,choose] at hSmall hBig hi hLenSmall hLenLarge
        simp only [code,encode_index,run,hSmall,hBig,Bool.false_eq_true,ite_false,right_index,hLenSmall,hLenLarge]
        rw [code,code,encode_index,encode_index] at hi
        omega

end Blotto.GeneralPaperQuantileOrdering
