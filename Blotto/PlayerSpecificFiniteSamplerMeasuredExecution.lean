import Blotto.PlayerSpecificFiniteAccuracyExecution
import Blotto.PlayerSpecificRationalFiniteMeasuredSourceCost
import Blotto.PlayerSpecificFiniteSamplerContract

/-! A measured public entry runs recognition, initial/minimum preparation,
all numerical precision choices, and one complete rational draw. -/
namespace Blotto.PlayerSpecificFiniteSamplerMeasuredExecution
open PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000
attribute [local irreducible] PlayerSpecificMinimumSearch.search

def frame {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ)
    (base : PlayerSpecificInitialMinimumExecution.Prepared N)
    (accuracy : PlayerSpecificFiniteAccuracy.Parameters) : Trace :=
  PlayerSpecificAlgebraicCallerFrame.run [[i.budget,epsilon]]
    [N,base.minimum.exponent,accuracy.scalarBits,accuracy.coinBits,
      accuracy.outputBits,
      PlayerSpecificAlgebraicFiniteDraw.bitCount N accuracy.coinBits accuracy.scalarBits]

def prepare {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ) :
    Option (PlayerSpecificFiniteSampler.Prepared N)×ℕ :=
  let model:=RationalCostModel.schoolbook
  let base:=PlayerSpecificInitialMinimumExecution.run i
  match base.1 with
  | none => (none,base.2+price model [.control 0])
  | some prepared =>
      let accuracy:=PlayerSpecificFiniteAccuracyExecution.run N prepared.minimum.exponent epsilon
      (some ⟨prepared,i.budget,accuracy.1⟩,
        base.2+accuracy.2+price model (frame i epsilon prepared accuracy.1)+
          price model [.control 1])

theorem prepare_value {N : ℕ} (i : RationalPlayerSpecificInput N) (epsilon : ℚ)
    (he : 0<epsilon) :
    (prepare i epsilon).1=PlayerSpecificFiniteSampler.prepare i epsilon := by
  cases hb : (PlayerSpecificInitialMinimumExecution.run i).1 with
  | none =>
    simp only [prepare,hb,PlayerSpecificFiniteSampler.prepare,Option.map_none]
  | some base =>
    simp only [prepare,hb,PlayerSpecificFiniteSampler.prepare,Option.map_some,
      PlayerSpecificFiniteAccuracyExecution.value N base.minimum.exponent epsilon he,
      PlayerSpecificFiniteSampler.ofBase]

def draw {N : ℕ} (p : PlayerSpecificFiniteSampler.Prepared N) (player : Bool)
    (bits : Fin (PlayerSpecificFiniteSampler.bitCount p) → Bool) :
    FixedArrayTable N ℚ×ℕ :=
  PlayerSpecificRationalFiniteMeasuredExecution.run p.base.initial p.budget player
    p.accuracy.coinBits p.accuracy.scalarBits p.accuracy.outputBits bits

theorem draw_value {N : ℕ} (p : PlayerSpecificFiniteSampler.Prepared N)
    (player : Bool) (bits : Fin (PlayerSpecificFiniteSampler.bitCount p) → Bool) :
    (draw p player bits).1=PlayerSpecificFiniteSampler.draw p player bits := by
  exact PlayerSpecificRationalFiniteMeasuredExecution.value p.base.initial p.budget player
    p.accuracy.coinBits p.accuracy.scalarBits p.accuracy.outputBits bits

end Blotto.PlayerSpecificFiniteSamplerMeasuredExecution
