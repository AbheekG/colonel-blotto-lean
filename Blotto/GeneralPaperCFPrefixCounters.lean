import Blotto.GeneralPaperClassifierEnvelope

/-! All-prefix counter bounds for the actual midpoint continued fraction.
The first zero quotient is treated once; every later prefix uses the
existing Euclidean depth potential. Prefix work is linear in lambda,
including the last rejected step, rather than quadratic full-fuel work.
-/
namespace Blotto.GeneralPaperCFPrefixCounters
open GeneralPaperRegularCFLoop GeneralPaperRegularCFFuel GeneralPaperCFFirstTerm
open GeneralPaperCFDepthPotential GeneralPaperMidpointRealWork
set_option autoImplicit false
set_option maxHeartbeats 6000000

theorem first_run (D C t lambda fuel : ℕ) (hD : 0<D) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) :
    run D (lambda+2) (fuel+1) (initial C t)=run D (lambda+2) fuel (first D C t lambda) := by
  change (if (advance D (lambda+2) (initial C t)).2 then
    run D (lambda+2) fuel (first D C t lambda) else first D C t lambda)=_
  rw [first_more D C t lambda hD hC ht hPower]
  rfl

theorem prefix_depth (D C t lambda fuel : ℕ) (hD : 0<D) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) :
    (run D (lambda+2) fuel (initial C t)).quotientDepth≤
      lambda+1+(run D (lambda+2) fuel (initial C t)).steps := by
  cases fuel with
  | zero => change 0≤lambda+1+0; omega
  | succ fuel =>
    have hPost := first_post D C t lambda hC ht hPower
    have he := run_depth_potential D lambda fuel (first D C t lambda) hPost.pair hPost.order
    rw [first_zero_depth D C t lambda hC ht,first_numerator D C t lambda hC ht hPower,
      ←first_run D C t lambda fuel hD hC ht hPower] at he
    have hBit := GeneralPaperCFOperandPrice.small_word lambda (2*C)
      (midpoint_pair_bound C t lambda hC ht hPower).2
    omega

theorem prefix_bounds (D C t lambda fuel : ℕ) (hD : 0<D) (hC : 0<C) (ht : t<C)
    (hPower : 8*C=2^lambda) (hFuel : fuel≤2*lambda+4) :
    let s := run D (lambda+2) fuel (initial C t)
    s.steps≤2*lambda+4 ∧ s.quotientDepth≤3*lambda+5 ∧ s.zeroChecks≤1 ∧ s.work≤170*lambda+338 := by
  have hs := run_step_count D (lambda+2) fuel (initial C t)
  have hd := prefix_depth D C t lambda fuel hD hC ht hPower
  have hz := run_zero_checks D (lambda+2) fuel (initial C t)
  have hw := initial_work D (lambda+2) fuel C t
  change (run D (lambda+2) fuel (initial C t)).steps≤0+fuel at hs
  change (run D (lambda+2) fuel (initial C t)).zeroChecks≤0+1 at hz
  dsimp only
  omega

theorem division_counters (n d divisionFuel : ℕ) :
    (GeneralPaperConstructedNatDivision.run n d divisionFuel).depth≤divisionFuel ∧
    (GeneralPaperConstructedNatDivision.run n d divisionFuel).work≤14*divisionFuel+16 := by
  have hd := GeneralPaperConstructedNatDivision.depth_le_fuel n d divisionFuel
  have hw := GeneralPaperConstructedNatDivision.work_depth n d divisionFuel
  exact ⟨hd,by omega⟩

theorem advance_bounds (D C t lambda fuel : ℕ) (hD : 0<D) (hC : 0<C) (ht : t<C)
    (hPower : 8*C=2^lambda) (hFuel : fuel≤2*lambda+4) :
    let s := (advance D (lambda+2) (run D (lambda+2) fuel (initial C t))).1
    s.steps≤2*lambda+5 ∧ s.quotientDepth≤4*lambda+7 ∧ s.zeroChecks≤2 ∧ s.work≤184*lambda+430 := by
  let s := run D (lambda+2) fuel (initial C t)
  have hb := prefix_bounds D C t lambda fuel hD hC ht hPower hFuel
  dsimp only at hb
  have hd := division_counters s.numerator s.denominator (lambda+2)
  change (advance D (lambda+2) s).1.steps≤_ ∧ (advance D (lambda+2) s).1.quotientDepth≤_ ∧
    (advance D (lambda+2) s).1.zeroChecks≤_ ∧ (advance D (lambda+2) s).1.work≤_
  change s.steps≤2*lambda+4 ∧ s.quotientDepth≤3*lambda+5 ∧ s.zeroChecks≤1 ∧ s.work≤170*lambda+338 at hb
  rw [advance]
  split
  · dsimp only
    omega
  · dsimp only
    split
    · split <;> dsimp only <;> omega
    · dsimp only
      omega

end Blotto.GeneralPaperCFPrefixCounters
