import Blotto.GeneralPaperCFDepthPotential

/-! The actual selected midpoint query has a linear source real-RAM work
profile. Adaptive quotient depths are amortized through an actual Euclidean
word-width potential, including the final rejected denominator. Full bit/
temporary-space calibration and the surrounding source ledger remain joins.
-/
namespace Blotto.GeneralPaperMidpointRealWork
open GeneralPaperRegularCFLoop GeneralPaperRegularCFFuel GeneralPaperCFFirstTerm
open GeneralPaperCFDepthPotential GeneralPaperMidpointQuery
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem raw_step_count (D C t lambda : ℕ) : (raw D C t lambda).steps≤2*lambda+4 := by
  have he := run_step_count D (lambda+2) (2*lambda+4) (initial C t)
  simpa only [raw,initial,Nat.zero_add] using he

theorem first_zero_depth (D C t lambda : ℕ) (hC : 0<C) (ht : t<C) : (first D C t lambda).quotientDepth=0 := by
  have hd : 0<(initial C t).denominator := by dsimp only [initial]; omega
  have hSmall : (((2*t+1:ℕ):ℚ))<((2*C:ℕ):ℚ) := by exact_mod_cast (show 2*t+1<2*C by omega)
  have he := (GeneralPaperGrowingQuotient.early_stop ((2*t+1:ℕ):ℚ) ((2*C:ℕ):ℚ) hSmall (lambda+1)).1
  have hDepth : (first D C t lambda).quotientDepth=
      (GeneralPaperConstructedNatDivision.run (2*t+1) (2*C) (lambda+2)).depth := by
    simpa only [first,initial,Nat.zero_add] using advance_depth_eq D (lambda+2) (initial C t) hd
  rw [hDepth]
  exact he

theorem first_numerator (D C t lambda : ℕ) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) :
    (first D C t lambda).numerator=2*C := by
  have hp := midpoint_pair_bound C t lambda hC ht hPower
  have hd : 0<(initial C t).denominator := by dsimp only [initial]; omega
  exact (advance_euclidean D (lambda+2) (initial C t) hd (quotient_cap lambda _ _ hp.1 hd)).1

theorem raw_quotient_depth (D C t lambda : ℕ) (hD : 0<D) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) :
    (raw D C t lambda).quotientDepth≤lambda+1+(raw D C t lambda).steps := by
  have hPost := first_post D C t lambda hC ht hPower
  have he := run_depth_potential D lambda (2*lambda+3) (first D C t lambda) hPost.pair hPost.order
  rw [first_zero_depth D C t lambda hC ht,first_numerator D C t lambda hC ht hPower,
    ←raw_first D C t lambda hD hC ht hPower] at he
  have hSize : 2*C<2^lambda := (midpoint_pair_bound C t lambda hC ht hPower).2
  have hBit : binaryWordWidth (2*C)≤lambda+1 := binaryWordWidth_le_of_lt_pow (Nat.succ_pos lambda)
    (hSize.trans_le (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (Nat.le_succ lambda)))
  omega

theorem lookup_real_work (D C t lambda : ℕ) (hD : 0<D) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) :
    (lookup D C t lambda).work≤170*lambda+370 := by
  have he := lookup_work_counter D C t lambda
  have hs := raw_step_count D C t lambda
  have hd := raw_quotient_depth D C t lambda hD hC ht hPower
  change (lookup D C t lambda).steps≤2*lambda+4 at hs
  change (lookup D C t lambda).quotientDepth≤lambda+1+(lookup D C t lambda).steps at hd
  omega

end Blotto.GeneralPaperMidpointRealWork
