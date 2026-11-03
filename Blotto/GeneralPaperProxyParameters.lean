import Blotto.GeneralPaperComparatorParameters

/-! Executed pre-call root-grid controls of the selected paper algorithm.
They depend only on the reduced field count and accuracy exponent. Powers
use repeated squaring; the grid is reached by doubling. The determinant
interpretation, classifier and complete bit/space prices are separate joins.
-/
namespace Blotto.GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 1500000

structure Parameters where
  K : ℕ
  S : ℕ
  d : ℕ
  H : ℕ
  Qg : ℕ
  gridBits : ℕ
  qbar : ℕ
  work : ℕ

def prepare (m k : ℕ) : Parameters :=
  let score := GeneralPaperScoreScaleParameters.prepare m k
  let dimension := m*(score.K-1)
  let determinant := GeneralPaperNatPower.run (m+3) (dimension+2)
  let grid := GeneralPaperPowerCeiling.ceiling (4*determinant.power*determinant.power)
  ⟨score.K,score.S,dimension,determinant.power,grid.power,grid.doublings,2*grid.power,
    score.work+determinant.work+grid.work+32⟩

theorem data (m k : ℕ) :
    (prepare m k).K=(GeneralPaperScoreScaleParameters.prepare m k).K ∧
    (prepare m k).S=(GeneralPaperScoreScaleParameters.prepare m k).S ∧
    (prepare m k).d=m*((prepare m k).K-1) ∧
    (prepare m k).H=(m+3)^((prepare m k).d+2) ∧
    (prepare m k).Qg=(GeneralPaperPowerCeiling.ceiling (4*(prepare m k).H*(prepare m k).H)).power ∧
    (prepare m k).gridBits=(GeneralPaperPowerCeiling.ceiling (4*(prepare m k).H*(prepare m k).H)).doublings ∧
    (prepare m k).qbar=2*(prepare m k).Qg := by
  simp only [prepare,(GeneralPaperNatPower.data _ _).1,and_self]

theorem H_positive (m k : ℕ) : 0<(prepare m k).H := by rw [(data m k).2.2.2.1]; positivity

theorem grid_lower (m k : ℕ) : 4*(prepare m k).H*(prepare m k).H≤(prepare m k).Qg := by
  rw [(data m k).2.2.2.2.1]
  exact GeneralPaperPowerCeiling.ceiling_lower _

theorem grid_positive (m k : ℕ) : 0<(prepare m k).Qg := by
  have hh := H_positive m k
  have hl := grid_lower m k
  nlinarith

theorem grid_upper (m k : ℕ) : (prepare m k).Qg<8*(prepare m k).H*(prepare m k).H := by
  rw [(data m k).2.2.2.2.1]
  have h := GeneralPaperPowerCeiling.ceiling_upper (4*(prepare m k).H*(prepare m k).H)
    (by have hh:=H_positive m k; positivity)
  nlinarith only [h]

theorem grid_power (m k : ℕ) : (prepare m k).Qg=2^(prepare m k).gridBits := by
  rw [(data m k).2.2.2.2.1,(data m k).2.2.2.2.2.1]
  exact GeneralPaperPowerCeiling.ceiling_power _

theorem cap_positive (m k : ℕ) : 0<(prepare m k).qbar := by
  rw [(data m k).2.2.2.2.2.2]
  exact Nat.mul_pos (by decide) (grid_positive m k)

theorem cap_upper (m k : ℕ) : (prepare m k).qbar≤16*(prepare m k).H*(prepare m k).H := by
  have hg := grid_upper m k
  rw [(data m k).2.2.2.2.2.2]
  nlinarith only [hg]

theorem prepare_work (m k : ℕ) :
    (prepare m k).work≤(GeneralPaperScoreScaleParameters.prepare m k).work+
      12*binaryWordWidth ((prepare m k).d+2)+
      12*binaryWordWidth (4*(prepare m k).H*(prepare m k).H)+36 := by
  have hd := GeneralPaperNatPower.work_bound (m+3) ((prepare m k).d+2)
  have hg := GeneralPaperPowerCeiling.ceiling_work (4*(prepare m k).H*(prepare m k).H)
  change (GeneralPaperScoreScaleParameters.prepare m k).work+
    (GeneralPaperNatPower.run (m+3) ((prepare m k).d+2)).work+
    (GeneralPaperPowerCeiling.ceiling (4*(prepare m k).H*(prepare m k).H)).work+32≤_
  omega

def alphabet (m k : ℕ) : GeneralPaperCodeAlphabet.Alphabet :=
  GeneralPaperComparatorParameters.alphabet m k (prepare m k).qbar (cap_positive m k)

end Blotto.GeneralPaperProxyParameters
