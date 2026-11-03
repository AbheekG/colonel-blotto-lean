import Blotto.GeneralPaperSourceWordGrowth

/-! Word bounds for constructed arithmetic values, including values too large
to be polynomial in the source parameters. Nested word bounds allow their
encoded lengths to have logarithmic word growth. Doubling and power results
use the native constructor correctness theorems, not runtime logarithms. -/
namespace Blotto.GeneralPaperConstructedWordGrowth
open GeneralPaperSourceWordGrowth
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

@[fun_prop]
theorem bits_small (f : Input → ℕ) (hf : Small f) : Small (fun x => GeneralPaperEncodedScalarStorage.natBits (f x)) := by
  unfold GeneralPaperEncodedScalarStorage.natBits
  fun_prop

@[fun_prop]
theorem bits_tight (f : Input → ℕ) (hf : Small f) : Tight (fun x => GeneralPaperEncodedScalarStorage.natBits (f x)) := by
  unfold GeneralPaperEncodedScalarStorage.natBits
  fun_prop

@[fun_prop]
theorem word_product (f g : Input → ℕ) (hf : Small (fun x => binaryWordWidth (f x)))
    (hg : Small (fun x => binaryWordWidth (g x))) : Small (fun x => binaryWordWidth (f x*g x)) :=
  dominated (small_add _ _ hf hg) (fun x => binaryWordWidth_mul (f x) (g x))

@[fun_prop]
theorem word_sum (f g : Input → ℕ) (hf : Small (fun x => binaryWordWidth (f x)))
    (hg : Small (fun x => binaryWordWidth (g x))) : Small (fun x => binaryWordWidth (f x+g x)) :=
  dominated (small_add _ _ hf hg) (fun x => GeneralPaperReferenceScaling.word_add (f x) (g x))

@[fun_prop]
theorem word_power (f n : Input → ℕ) (hf : Small (fun x => binaryWordWidth (f x))) (hn : Small n) :
    Small (fun x => binaryWordWidth ((f x)^(n x))) := by
  apply dominated (g:=fun x => 1+n x*binaryWordWidth (f x))
  · fun_prop
  · intro x
    exact GeneralPaperFastRationalBounds.word_power _ _

@[fun_prop]
theorem ceiling_power (f : Input → ℕ) (hf : Small f) :
    Small (fun x => (GeneralPaperPowerCeiling.ceiling (f x)).power) := by
  rcases hf with ⟨C,hC⟩
  refine ⟨C+4,?_⟩
  intro x
  have hw := GeneralPaperParameterOperandBounds.ceiling_word (f x)
  have hc := hC x
  have hs := size_positive x
  nlinarith only [hw,hc,hs]

@[fun_prop]
theorem ceiling_word (f : Input → ℕ) (hf : Small (fun x => binaryWordWidth (f x))) :
    Small (fun x => binaryWordWidth (GeneralPaperPowerCeiling.ceiling (f x)).power) := by
  apply dominated (g:=fun x => 4+binaryWordWidth (f x))
  · fun_prop
  · intro x
    exact GeneralPaperParameterOperandBounds.ceiling_word _

theorem ceiling_depth_bound (n : ℕ) : (GeneralPaperPowerCeiling.ceiling n).doublings≤binaryWordWidth n :=
  GeneralPaperPowerCeiling.ceiling_minimal _ _ (lt_pow_binaryWordWidth _).le

@[fun_prop]
theorem ceiling_depth_tight (f : Input → ℕ) (hf : Small f) :
    Tight (fun x => (GeneralPaperPowerCeiling.ceiling (f x)).doublings) := by
  rcases hf with ⟨C,hC⟩
  exact ⟨C,fun x => (ceiling_depth_bound _).trans (hC x)⟩

@[fun_prop]
theorem ceiling_depth_small (f : Input → ℕ) (hf : Small (fun x => binaryWordWidth (f x))) :
    Small (fun x => (GeneralPaperPowerCeiling.ceiling (f x)).doublings) :=
  dominated hf (fun _x => ceiling_depth_bound _)

@[fun_prop]
theorem ceiling_work_tight (f : Input → ℕ) (hf : Small f) :
    Tight (fun x => (GeneralPaperPowerCeiling.ceiling (f x)).work) := by
  rcases hf with ⟨C,hC⟩
  refine ⟨12*C+2,?_⟩
  intro x
  have hw := GeneralPaperPowerCeiling.ceiling_work (f x)
  have hc := hC x
  have hs := size_positive x
  nlinarith only [hw,hc,hs]

@[fun_prop]
theorem ceiling_work_small (f : Input → ℕ) (hf : Small (fun x => binaryWordWidth (f x))) :
    Small (fun x => (GeneralPaperPowerCeiling.ceiling (f x)).work) := by
  apply dominated (g:=fun x => 12*binaryWordWidth (f x)+2)
  · fun_prop
  · intro x
    exact GeneralPaperPowerCeiling.ceiling_work _

@[fun_prop]
theorem dyadic_power (f : Input → ℕ) (hf : Tight f) :
    Small (fun x => (GeneralPaperScoreScaleParameters.powerRun (f x)).power) := by
  have he : (fun x => (GeneralPaperScoreScaleParameters.powerRun (f x)).power)=(fun x => 2^(f x)) :=
    funext (fun x => (GeneralPaperScoreScaleParameters.power_data _).1)
  rw [he]
  fun_prop

@[fun_prop]
theorem dyadic_depth_tight (f : Input → ℕ) (hf : Tight f) :
    Tight (fun x => (GeneralPaperScoreScaleParameters.powerRun (f x)).doublings) := by
  have he : (fun x => (GeneralPaperScoreScaleParameters.powerRun (f x)).doublings)=f :=
    funext (fun x => (GeneralPaperScoreScaleParameters.power_data _).2.1)
  rw [he]
  exact hf

@[fun_prop]
theorem dyadic_depth_small (f : Input → ℕ) (hf : Small f) :
    Small (fun x => (GeneralPaperScoreScaleParameters.powerRun (f x)).doublings) := by
  have he : (fun x => (GeneralPaperScoreScaleParameters.powerRun (f x)).doublings)=f :=
    funext (fun x => (GeneralPaperScoreScaleParameters.power_data _).2.1)
  rw [he]
  exact hf

@[fun_prop]
theorem dyadic_work_tight (f : Input → ℕ) (hf : Tight f) :
    Tight (fun x => (GeneralPaperScoreScaleParameters.powerRun (f x)).work) := by
  have he : (fun x => (GeneralPaperScoreScaleParameters.powerRun (f x)).work)=(fun x => 8*f x+2) :=
    funext (fun x => (GeneralPaperScoreScaleParameters.power_data _).2.2)
  rw [he]
  fun_prop

@[fun_prop]
theorem dyadic_work_small (f : Input → ℕ) (hf : Small f) :
    Small (fun x => (GeneralPaperScoreScaleParameters.powerRun (f x)).work) := by
  have he : (fun x => (GeneralPaperScoreScaleParameters.powerRun (f x)).work)=(fun x => 8*f x+2) :=
    funext (fun x => (GeneralPaperScoreScaleParameters.power_data _).2.2)
  rw [he]
  fun_prop

@[fun_prop]
theorem natural_power_word (f n : Input → ℕ) (hf : Small (fun x => binaryWordWidth (f x))) (hn : Small n) :
    Small (fun x => binaryWordWidth (GeneralPaperNatPower.run (f x) (n x)).power) := by
  have he : (fun x => binaryWordWidth (GeneralPaperNatPower.run (f x) (n x)).power)=
      (fun x => binaryWordWidth ((f x)^(n x))) :=
    funext (fun x => congrArg binaryWordWidth (GeneralPaperNatPower.data _ _).1)
  rw [he]
  fun_prop

@[fun_prop]
theorem natural_power_work (f n : Input → ℕ) (hn : Small n) :
    Small (fun x => (GeneralPaperNatPower.run (f x) (n x)).work) := by
  apply dominated (g:=fun x => 12*binaryWordWidth (n x)+2)
  · fun_prop
  · intro x
    exact GeneralPaperNatPower.work_bound _ _

@[fun_prop]
theorem fast_charge (C d : ℕ) (f : Input → ℕ) (hf : Small f) :
    Small (fun x => GeneralPaperFastRationalModel.charge C d (f x)) := by
  unfold GeneralPaperFastRationalModel.charge GeneralPaperFastRationalModel.logFactor
  fun_prop

@[fun_prop]
theorem expression_height (f h : Input → ℕ) (hf : Small f) (hh : Tight h) :
    Small (fun x => expressionHeightBudget (f x) (h x)) := by
  unfold expressionHeightBudget
  fun_prop

end Blotto.GeneralPaperConstructedWordGrowth
