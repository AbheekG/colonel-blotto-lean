import Blotto.GeneralPaperNatPower
import Blotto.GeneralPaperSourceParameters
import Blotto.GeneralPaperCodeAlphabet

/-! Constructed K_c, J_D, D, C and Lambda of the selected paper source.
The proxy denominator cap qbar is an explicit input from the later proxy/root
constructor. No comparator polytope or real probabilities are computed.
Counters here are arithmetic operations; bit/space joins remain separate.
-/
namespace Blotto.GeneralPaperComparatorParameters
open GeneralPaperCodeAlphabet
set_option autoImplicit false
set_option maxHeartbeats 1500000

def countRun (k : ℕ) := GeneralPaperScoreScaleParameters.powerRun (17+k)

theorem count_power (k : ℕ) : (countRun k).power=2^(17+k) :=
  (GeneralPaperScoreScaleParameters.power_data (17+k)).1

theorem count_positive (k : ℕ) : 0<(countRun k).power := by rw [count_power]; positivity

theorem count_error (k : ℕ) :
    1/((countRun k).power:ℝ)=((GeneralPaperSourceParameters.prepare k).z:ℝ)/64 := by
  rw [count_power,(GeneralPaperSourceParameters.data k).1]
  push_cast
  simp only [pow_add]
  norm_num
  ring

structure Parameters where
  Kc : ℕ
  J : ℕ
  D : ℕ
  C : ℕ
  lambda : ℕ
  work : ℕ

def prepare (m k qbar : ℕ) : Parameters :=
  let labels := countRun k
  let dimension := m*(labels.power-1)+1
  let determinant := GeneralPaperNatPower.run (m+2) dimension
  let denominator := qbar*determinant.power
  let scale := GeneralPaperPowerCeiling.ceiling (4*denominator*denominator)
  ⟨labels.power,dimension,denominator,scale.power,scale.doublings+3,
    labels.work+determinant.work+scale.work+32⟩

theorem data (m k qbar : ℕ) :
    (prepare m k qbar).Kc=(countRun k).power ∧
    (prepare m k qbar).J=m*((countRun k).power-1)+1 ∧
    (prepare m k qbar).D=qbar*(m+2)^(m*((countRun k).power-1)+1) ∧
    (prepare m k qbar).C=(GeneralPaperPowerCeiling.ceiling (4*(prepare m k qbar).D*(prepare m k qbar).D)).power ∧
    (prepare m k qbar).lambda=(GeneralPaperPowerCeiling.ceiling (4*(prepare m k qbar).D*(prepare m k qbar).D)).doublings+3 := by
  simp only [prepare,(GeneralPaperNatPower.data _ _).1,and_self]

theorem denominator_positive (m k qbar : ℕ) (hq : 0<qbar) : 0<(prepare m k qbar).D := by
  rw [(data m k qbar).2.2.1]
  exact Nat.mul_pos hq (by positivity)

def alphabet (m k qbar : ℕ) (hq : 0<qbar) : Alphabet where
  D := (prepare m k qbar).D
  C := (prepare m k qbar).C
  lambda := (prepare m k qbar).lambda
  orderPositive := denominator_positive m k qbar hq
  scalePositive := by
    have hd := denominator_positive m k qbar hq
    have hs := GeneralPaperPowerCeiling.ceiling_lower (4*(prepare m k qbar).D*(prepare m k qbar).D)
    rw [← (data m k qbar).2.2.2.1] at hs
    nlinarith
  separated := by
    have hs := GeneralPaperPowerCeiling.ceiling_lower (4*(prepare m k qbar).D*(prepare m k qbar).D)
    rw [← (data m k qbar).2.2.2.1] at hs
    nlinarith
  dyadic := by
    rw [(data m k qbar).2.2.2.1,(data m k qbar).2.2.2.2,GeneralPaperPowerCeiling.ceiling_power,pow_add]
    norm_num
    omega

theorem denominator_cap (m k q qbar : ℕ) (hq : 0<qbar) (hCap : q≤qbar) :
    q*(m+2)^(m*((countRun k).power-1)+1)≤(alphabet m k qbar hq).D := by
  change _≤(prepare m k qbar).D
  rw [(data m k qbar).2.2.1]
  exact Nat.mul_le_mul_right _ hCap

theorem grid_scale_lower (m k qbar : ℕ) (hq : 0<qbar) :
    4*(alphabet m k qbar hq).D^2≤(alphabet m k qbar hq).C := by
  change 4*(prepare m k qbar).D^2≤(prepare m k qbar).C
  rw [(data m k qbar).2.2.2.1]
  simpa only [pow_two,Nat.mul_assoc] using
    GeneralPaperPowerCeiling.ceiling_lower (4*(prepare m k qbar).D*(prepare m k qbar).D)

theorem prepare_work (m k qbar : ℕ) :
    (prepare m k qbar).work≤8*(17+k)+
      12*binaryWordWidth (m*((countRun k).power-1)+1)+
      12*binaryWordWidth (4*(prepare m k qbar).D*(prepare m k qbar).D)+38 := by
  have hl := (GeneralPaperScoreScaleParameters.power_data (17+k)).2.2
  have hd := GeneralPaperNatPower.work_bound (m+2) (m*((countRun k).power-1)+1)
  have hs := GeneralPaperPowerCeiling.ceiling_work (4*(prepare m k qbar).D*(prepare m k qbar).D)
  change (countRun k).work=8*(17+k)+2 at hl
  change (countRun k).work+(GeneralPaperNatPower.run (m+2) (m*((countRun k).power-1)+1)).work+
    (GeneralPaperPowerCeiling.ceiling (4*(prepare m k qbar).D*(prepare m k qbar).D)).work+32≤_
  omega

end Blotto.GeneralPaperComparatorParameters
