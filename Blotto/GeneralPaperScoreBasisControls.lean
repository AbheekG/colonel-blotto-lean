import Blotto.GeneralPaperScoreMatrixEnvelope

/-! A constructed logarithmic local word covers the score matrix and
native basis-loop counters. This is not yet the global source/pointer/
parameter capacity or simultaneous working-space theorem.
-/
namespace Blotto.GeneralPaperScoreBasisControls
open GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 5000000

def word (m k : ℕ) : ℕ := 2+(GeneralPaperScoreScaleParameters.prepare m k).depth+
  binaryWordWidth (m*((prepare m k).K-1)+3)+binaryWordWidth ((prepare m k).S+2)+
  binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)+binaryWordWidth ((prepare m k).S+4)

theorem capacities (m k : ℕ) :
    1≤word m k ∧ binaryWordWidth (m*((prepare m k).K-1)+3)≤word m k ∧
    binaryWordWidth ((prepare m k).S+2)≤word m k ∧
    binaryWordWidth (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)+3)≤word m k ∧
    binaryWordWidth ((prepare m k).S+4)≤word m k ∧
    (GeneralPaperScoreScaleParameters.prepare m k).depth+2≤word m k := by
  unfold word
  omega

theorem field_label (m k : ℕ) (hm : 0<m) :
    binaryWordWidth ((prepare m k).K+1)≤word m k ∧ binaryWordWidth (m+1)≤word m k :=
  (GeneralPaperBasisBitEnvelope.index_capacities m k (word m k) hm (capacities m k).2.1).2

theorem depth (m k : ℕ) :
    (GeneralPaperScoreScaleParameters.prepare m k).depth≤binaryWordWidth (prepare m k).S+1 := by
  have hl := GeneralPaperScoreScaleParameters.scale_lower m k
  have hd := GeneralPaperScoreScaleParameters.depth_bound m k
  have hw := binaryWordWidth_mono hl
  simpa only [(data m k).2.1] using hd.trans (Nat.add_le_add_right hw 1)

theorem word_bound (m k : ℕ) (hm : 0<m) :
    word m k≤8*(binaryWordWidth (m*((prepare m k).K-1)+3)+binaryWordWidth ((prepare m k).S+4)+1) := by
  have hd := depth m k
  have hk := (binaryWordWidth_mono (show (prepare m k).K≤(prepare m k).K+1 by omega)).trans
    (binaryWordWidth_mono (GeneralPaperBasisBitEnvelope.dimension_bounds m k hm).2)
  have hs := binaryWordWidth_mono (show (prepare m k).S≤(prepare m k).S+4 by omega)
  have hs1 := binaryWordWidth_mono (show (prepare m k).S+1≤(prepare m k).S+4 by omega)
  have hs2 := binaryWordWidth_mono (show (prepare m k).S+2≤(prepare m k).S+4 by omega)
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add (((prepare m k).S+1)*((prepare m k).K*(prepare m k).K)) 3
  have hb := binaryWordWidth_mul ((prepare m k).S+1) ((prepare m k).K*(prepare m k).K)
  have hc := binaryWordWidth_mul (prepare m k).K (prepare m k).K
  have h3 : binaryWordWidth 3=2 := by decide
  unfold word
  omega

theorem quotient_words {m K : ℕ} (v : RationalFieldSelector m) (S : ℕ) (hK : 0<K)
    (j : Fin m) (l : Fin K) (w W : ℕ) (hCap : S<2^w) (hW : w+1≤W) :
    binaryWordWidth (GeneralPaperBoundedQuotient.run (GeneralPaperScoreMatrixWork.argument v S j l) 1 w).quotient≤W := by
  have hb := GeneralPaperScoreMatrixWork.argument_bounds v S hK j l
  have hc : GeneralPaperScoreMatrixWork.argument v S j l<(1:ℚ)*(2:ℚ)^w := by
    have hs : (S:ℚ)<(2:ℚ)^w := by exact_mod_cast hCap
    simpa only [one_mul] using hb.2.trans_lt hs
  exact (GeneralPaperBoundedQuotient.quotient_words _ 1 (by norm_num) w hb.1 hc).trans hW

end Blotto.GeneralPaperScoreBasisControls
