import Blotto.GeneralPaperQuantileChildMass

/-! The actual single-path descent preserves both exact quantile endpoints.
The running rounded prefix is allowed to have a different error exponent at
each depth. All comparisons use the freshly computed common total mass.
-/
namespace Blotto.GeneralPaperQuantileBracket
open GeneralPaperDyadicFloat GeneralPaperPreparedPowers GeneralPaperMassApproximation
open GeneralPaperIntervalCache GeneralPaperIntervalLevels GeneralPaperGlobalNodeQuery
open GeneralPaperTreePrefix GeneralPaperQuantileDescent GeneralPaperQuantilePath
open GeneralPaperNormalizedMassError GeneralPaperQuantileComparison
set_option autoImplicit false
set_option maxHeartbeats 3500000

def Bracket (P M T target tolerance : ℚ) : Prop :=
  P/T≤target+tolerance ∧ target-tolerance≤(P+M)/T

theorem run_bracket (lambda k j : ℕ) (hJ : j≤(GeneralPaperSourceParameters.prepare k).summarySize)
    (storedTotal : Number) (T : ℚ) (hT : 0<T)
    (hTotal : Bound (prepare lambda k).format.unit (queryExponent lambda k) T storedTotal)
    (height : ℕ) (node : Node height) (ancestor depth : ℕ) (P : ℚ) (storedMass storedPrefix : Number)
    (hDepth : height+depth≤lambda+1) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) ancestor node)
    (hMass : Bound (prepare lambda k).format.unit (queryExponent lambda k) (trueMass k ancestor node) storedMass)
    (hPrefix : Bound (prepare lambda k).format.unit (queryExponent lambda k+depth) P storedPrefix)
    (hDomain : P+trueMass k ancestor node≤T)
    (hBracket : Bracket P (trueMass k ancestor node) T
      ((j:ℚ)/(GeneralPaperSourceParameters.prepare k).summarySize) (delta k)) :
    let result := run (prepare lambda k) (width lambda k) j (GeneralPaperSourceParameters.prepare k).summarySize
      storedTotal height node ancestor storedMass storedPrefix
    (P+weightedPrefix k ancestor node (index result.path))/T≤
        (j:ℚ)/(GeneralPaperSourceParameters.prepare k).summarySize+delta k ∧
      (j:ℚ)/(GeneralPaperSourceParameters.prepare k).summarySize-delta k≤
        (P+weightedPrefix k ancestor node (index result.path+1))/T := by
  induction height generalizing ancestor depth P storedMass storedPrefix with
  | zero =>
    dsimp only [run,index]
    simp only [Nat.zero_add]
    rw [weighted_zero,add_zero]
    have ht := weighted_total k ancestor node
    simp only [pow_zero] at ht
    rw [ht]
    exact hBracket
  | succ height ih =>
    let left := leftMass (prepare lambda k) ancestor node storedMass
    let through := GeneralPaperDyadicAddition.add (prepare lambda k).format.unit
      (prepare lambda k).format.fractionalBits storedPrefix left.number
    let L := trueMass k (ancestor+offset node) (leftChild node)
    let R := trueMass k (ancestor+offset node) (rightChild node)
    have hL : 0<L := true_positive _ _ _
    have hR : 0<R := true_positive _ _ _
    have hSplit : trueMass k ancestor node=L+R := true_split k ancestor node
    have hLeft := GeneralPaperQuantileChildMass.left_bound lambda k ancestor node storedMass (by omega) hValid hPath hMass
    have hWeaken := weaken _ _ (queryExponent lambda k+depth) _ _ (GeneralPaperPowerPrecision.unit_positive lambda k)
      (Nat.le_add_right _ _) hLeft
    have hThrough : Bound (prepare lambda k).format.unit (queryExponent lambda k+(depth+1)) (P+L) through.number := by
      exact add_bound _ _ _ (GeneralPaperPowerPrecision.unit_positive lambda k)
        (GeneralPaperPowerPrecision.unit_power lambda k) P L storedPrefix left.number hPrefix hWeaken
    have hChoices := choose_branches lambda k j (queryExponent lambda k+(depth+1)) (queryExponent lambda k)
      through.number storedTotal (P+L) T hJ hT (by rw [hSplit] at hDomain; linarith)
      (by unfold budget; omega) (by unfold budget; omega) hThrough hTotal
    have hChildren := child_validity lambda k node hValid
    have hPaths := child_paths _ ancestor node hPath
    rw [run]
    split
    · rename_i hChoose
      dsimp only
      have hPrefix' := weaken _ _ (queryExponent lambda k+(depth+1)) _ _
        (GeneralPaperPowerPrecision.unit_positive lambda k) (by omega) hPrefix
      have hBracket' : Bracket P L T ((j:ℚ)/(GeneralPaperSourceParameters.prepare k).summarySize) (delta k) :=
        ⟨hBracket.1,hChoices.1 hChoose⟩
      have hi := ih (leftChild node) (ancestor+offset node) (depth+1) P left.number storedPrefix
        (by omega) hChildren.1 hPaths.1 hLeft hPrefix' (by rw [hSplit] at hDomain; linarith) hBracket'
      have hLen := path_length (prepare lambda k) (width lambda k) j
        (GeneralPaperSourceParameters.prepare k).summarySize storedTotal height (leftChild node)
        (ancestor+offset node) left.number storedPrefix
      have hIndex := index_bound (run (prepare lambda k) (width lambda k) j
        (GeneralPaperSourceParameters.prepare k).summarySize storedTotal height (leftChild node)
        (ancestor+offset node) left.number storedPrefix).path
      rw [hLen] at hIndex
      let a := index (run (prepare lambda k) (width lambda k) j
        (GeneralPaperSourceParameters.prepare k).summarySize storedTotal height (leftChild node)
        (ancestor+offset node) left.number storedPrefix).path
      rw [left_index]
      change (P+weightedPrefix k ancestor node a)/T≤_ ∧ _≤(P+weightedPrefix k ancestor node (a+1))/T
      rw [weighted_left k ancestor node a hIndex.le,
        weighted_left k ancestor node (a+1) (by exact Nat.succ_le_of_lt hIndex)]
      exact hi
    · rename_i hChoose
      dsimp only
      have hRight := GeneralPaperQuantileChildMass.right_bound lambda k ancestor node storedMass (by omega) hValid hPath hMass
      have hBracket' : Bracket (P+L) R T ((j:ℚ)/(GeneralPaperSourceParameters.prepare k).summarySize) (delta k) := by
        have hFalse : (choose lambda k j storedTotal through.number).answer=false := by
          cases hc : (choose lambda k j storedTotal through.number).answer
          · rfl
          · exact False.elim (hChoose hc)
        refine ⟨hChoices.2 hFalse,?_⟩
        simpa only [hSplit,add_assoc] using hBracket.2
      have hi := ih (rightChild node) (ancestor+offset node) (depth+1) (P+L)
        (rightMass (prepare lambda k) ancestor node storedMass).number through.number
        (by omega) hChildren.2 hPaths.2 hRight hThrough (by rw [hSplit] at hDomain; linarith) hBracket'
      have hLen := path_length (prepare lambda k) (width lambda k) j
        (GeneralPaperSourceParameters.prepare k).summarySize storedTotal height (rightChild node)
        (ancestor+offset node) (rightMass (prepare lambda k) ancestor node storedMass).number through.number
      have hIndex := index_bound (run (prepare lambda k) (width lambda k) j
        (GeneralPaperSourceParameters.prepare k).summarySize storedTotal height (rightChild node)
        (ancestor+offset node) (rightMass (prepare lambda k) ancestor node storedMass).number through.number).path
      rw [hLen] at hIndex
      let a := index (run (prepare lambda k) (width lambda k) j
        (GeneralPaperSourceParameters.prepare k).summarySize storedTotal height (rightChild node)
        (ancestor+offset node) (rightMass (prepare lambda k) ancestor node storedMass).number through.number).path
      rw [right_index,hLen]
      change (P+weightedPrefix k ancestor node (2^height+a))/T≤_ ∧
        _≤(P+weightedPrefix k ancestor node (2^height+a+1))/T
      rw [weighted_right k ancestor node a hIndex.le,show 2^height+a+1=2^height+(a+1) by omega,
        weighted_right k ancestor node (a+1) (Nat.succ_le_of_lt hIndex)]
      simpa only [add_assoc] using hi

end Blotto.GeneralPaperQuantileBracket
