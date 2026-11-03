import Blotto.GeneralPaperCFControlWords

/-! One explicit logarithmic control-word calibration for the prepared
score/root/alphabet constructors and their classifiers. Constructed widths
occur only in this proof calibration; no original encoding query is run.
Large arithmetic values remain separately priced by their operand lengths.
-/
namespace Blotto.GeneralPaperPrecallControlWord
set_option autoImplicit false
set_option maxHeartbeats 6000000

def measure (m k : ℕ) : ℕ :=
  let s := GeneralPaperScoreScaleParameters.prepare m k
  let r := GeneralPaperProxyParameters.prepare m k
  let a := GeneralPaperComparatorParameters.prepare m k r.qbar
  (k+18)+(binaryWordWidth (m*s.K)+1)+(binaryWordWidth (r.d+2)+1)+
    (binaryWordWidth (4*r.H*r.H)+1)+(binaryWordWidth a.J+1)+
    (binaryWordWidth (4*a.D*a.D)+1)+(r.gridBits+4)

def cap (m k : ℕ) : ℕ := 4096*(measure m k+1)+16384
def word (m k : ℕ) : ℕ := 128+8*binaryWordWidth (measure m k+1)

theorem terms (m k : ℕ) :
    let s := GeneralPaperScoreScaleParameters.prepare m k
    let r := GeneralPaperProxyParameters.prepare m k
    let a := GeneralPaperComparatorParameters.prepare m k r.qbar
    k+18≤measure m k ∧ binaryWordWidth (m*s.K)+1≤measure m k ∧
    binaryWordWidth (r.d+2)+1≤measure m k ∧ binaryWordWidth (4*r.H*r.H)+1≤measure m k ∧
    binaryWordWidth a.J+1≤measure m k ∧ binaryWordWidth (4*a.D*a.D)+1≤measure m k ∧
    r.gridBits+4≤measure m k := by
  dsimp only
  unfold measure
  dsimp only
  omega

theorem bounded (m k n : ℕ) (hn : n≤cap m k) : 64+binaryWordWidth n≤word m k := by
  have hm := binaryWordWidth_mul 4096 (measure m k+1)
  have ha := GeneralPaperRayOperandWidthEnvelope.word_add (4096*(measure m k+1)) 16384
  have h4096 : binaryWordWidth 4096=13 := by decide
  have h16384 : binaryWordWidth 16384=15 := by decide
  have hb := binaryWordWidth_mono hn
  unfold cap at hb
  unfold word
  omega

theorem measured (m k n : ℕ) (hn : n≤measure m k) : 64+binaryWordWidth n≤word m k :=
  bounded m k n (by unfold cap; omega)

theorem score_controls (m k : ℕ) :
    let s := GeneralPaperScoreScaleParameters.prepare m k
    s.depth≤measure m k ∧ s.work≤20*measure m k+20 := by
  have ht := terms m k
  dsimp only at ht ⊢
  have hd := GeneralPaperScoreScaleParameters.depth_bound m k
  have hw := GeneralPaperScoreScaleParameters.prepare_work m k
  omega

theorem root_controls (m k : ℕ) :
    let r := GeneralPaperProxyParameters.prepare m k
    r.gridBits+4≤measure m k ∧ r.work≤44*measure m k+56 := by
  have ht := terms m k
  have hs := score_controls m k
  have hw := GeneralPaperProxyParameters.prepare_work m k
  dsimp only at ht hs ⊢
  omega

theorem alphabet_controls (m k : ℕ) :
    let r := GeneralPaperProxyParameters.prepare m k
    let a := GeneralPaperComparatorParameters.prepare m k r.qbar
    a.lambda≤measure m k+2 ∧ a.work≤32*measure m k+38 := by
  let r := GeneralPaperProxyParameters.prepare m k
  let a := GeneralPaperComparatorParameters.prepare m k r.qbar
  have ht := terms m k
  dsimp only at ht
  have hw := GeneralPaperComparatorParameters.prepare_work m k r.qbar
  have hd := GeneralPaperPowerCeiling.loop_depth (4*a.D*a.D) 1 (by decide)
  change (GeneralPaperPowerCeiling.ceiling (4*a.D*a.D)).doublings≤binaryWordWidth (4*a.D*a.D) at hd
  have hLambda : a.lambda=(GeneralPaperPowerCeiling.ceiling (4*a.D*a.D)).doublings+3 :=
    (GeneralPaperComparatorParameters.data m k r.qbar).2.2.2.2
  change a.lambda≤measure m k+2 ∧ a.work≤32*measure m k+38
  change a.work≤8*(17+k)+12*binaryWordWidth a.J+12*binaryWordWidth (4*a.D*a.D)+38 at hw
  dsimp only [r,a] at *
  omega

theorem metadata (m k : ℕ) :
    let s := GeneralPaperScoreScaleParameters.prepare m k
    let r := GeneralPaperProxyParameters.prepare m k
    let a := GeneralPaperComparatorParameters.prepare m k r.qbar
    binaryWordWidth (s.depth+4)≤word m k ∧ binaryWordWidth (s.work+512)≤word m k ∧
    binaryWordWidth (r.gridBits+8)≤word m k ∧ binaryWordWidth (r.work+512)≤word m k ∧
    binaryWordWidth (a.lambda+8)≤word m k ∧ binaryWordWidth (a.work+512)≤word m k := by
  have hs := score_controls m k
  have hr := root_controls m k
  have ha := alphabet_controls m k
  dsimp only at hs hr ha ⊢
  have bound (n : ℕ) (hn : n≤cap m k) : binaryWordWidth n≤word m k := by
    have hh := bounded m k n hn
    omega
  refine ⟨bound _ ?_,bound _ ?_,bound _ ?_,bound _ ?_,bound _ ?_,bound _ ?_⟩ <;>
    unfold cap <;> omega

end Blotto.GeneralPaperPrecallControlWord
