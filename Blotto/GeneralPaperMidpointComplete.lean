import Blotto.GeneralPaperCFFirstTerm

/-! Completeness of the actual arithmetic midpoint query. The executed
continuants agree with regular convergents, bounded future denominators
cannot be skipped, and the retained error does not increase. Legendre's
criterion therefore puts every nonempty bucket's unique Farey value into
the endpoint-tested output. No existence, convergent or retention oracle
is supplied to the executed query.
-/
namespace Blotto.GeneralPaperMidpointComplete
open GeneralPaperRegularCFLoop GeneralPaperRegularCFFuel GeneralPaperCFError
open GeneralPaperCFFirstTerm GeneralPaperCFRetention GeneralPaperBucketGeometry GeneralPaperMidpointQuery
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem midpoint_error (C t : ℕ) (value : ℚ) :
    valueError (2*t+1) (2*C) value=|GeneralPaperBucketGeometry.midpoint C t-value| := by
  simp only [valueError,GeneralPaperBucketGeometry.midpoint,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]

theorem distance_interior (C t : ℕ) (hC : 0<C) (value : ℚ)
    (hDistance : |GeneralPaperBucketGeometry.midpoint C t-value|<1/(2*(C:ℚ))) : Interior C t value := by
  have hAbs := abs_lt.mp hDistance
  have hl := midpoint_left C t hC
  have hr := midpoint_right C t hC
  exact ⟨by linarith only [hAbs.2,hl],by linarith only [hAbs.1,hr]⟩

theorem bounded_convergent_dominance (D C t lambda : ℕ) (hD : 0<D) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda)
    (k : ℕ) (hBound : (Real.convergent (((2*t+1:ℕ):ℝ)/((2*C:ℕ):ℝ)) k).den≤D) :
    ∃ f, (raw D C t lambda).selected=some f ∧
      valueError (2*t+1) (2*C) f.value≤
        valueError (2*t+1) (2*C) (Real.convergent (((2*t+1:ℕ):ℝ)/((2*C:ℕ):ℝ)) k) := by
  have hM : 0<2*C := by omega
  have hPost := first_post D C t lambda hC ht hPower
  have hSelected := first_selected D C t lambda hD hC ht hPower
  have hStops := first_stops D C t lambda hD hC ht hPower
  have hRawBound : (GeneralPaperCFModel.future (GeneralPaperCFModel.initial (2*t+1) (2*C)) k).2≤D := by
    rw [GeneralPaperCFModel.initial_future (2*t+1) (2*C) k hM]
    have he := GeneralPaperCFReference.reduced_denominator (2*t+1) (2*C) k hM
    rw [GeneralPaperCFReference.value_eq_regular (2*t+1) (2*C) k hM] at he
    rw [←he]
    exact hBound
  cases k with
  | zero =>
    obtain ⟨f,hf,he⟩ := run_selected_dominance D (2*t+1) (2*C) lambda (2*lambda+3) _ hM hPost hSelected
    have hZero : Real.convergent (((2*t+1:ℕ):ℝ)/((2*C:ℕ):ℝ)) 0=0 := by
      rw [←GeneralPaperCFReference.value_eq_regular (2*t+1) (2*C) 0 hM]
      simp only [GeneralPaperCFReference.pair,Nat.div_eq_of_lt (show 2*t+1<2*C by omega),Nat.cast_zero,zero_div]
    have hFields := first_fields D C t lambda hC ht hPower
    refine ⟨f,?_,?_⟩
    · rw [raw_first D C t lambda hD hC ht hPower]
      exact hf
    · simpa only [currentError,hFields.1,hFields.2.1,Nat.cast_zero,zero_div,hZero] using he
  | succ k =>
    have hFuture : GeneralPaperCFModel.future (GeneralPaperCFModel.initial (2*t+1) (2*C)) (k+1)=
        GeneralPaperCFModel.future (GeneralPaperCFModel.view (first D C t lambda)) k := by
      rw [GeneralPaperCFModel.future_succ,←first_view D C t lambda hC ht hPower]
    have hNextBound : (GeneralPaperCFModel.future (GeneralPaperCFModel.view (first D C t lambda)) k).2≤D := by
      rw [←hFuture]
      exact hRawBound
    obtain ⟨f,hf,he⟩ := run_future_dominance D (2*t+1) (2*C) lambda (2*lambda+3) _ hM hPost hSelected hStops k hNextBound
    have hValue : (((GeneralPaperCFModel.future (GeneralPaperCFModel.view (first D C t lambda)) k).1:ℚ)/
        (GeneralPaperCFModel.future (GeneralPaperCFModel.view (first D C t lambda)) k).2)=
        Real.convergent (((2*t+1:ℕ):ℝ)/((2*C:ℕ):ℝ)) (k+1) := by
      rw [←hFuture]
      exact GeneralPaperCFModel.initial_value_eq_regular (2*t+1) (2*C) (k+1) hM
    rw [hValue] at he
    refine ⟨f,?_,he⟩
    rw [raw_first D C t lambda hD hC ht hPower]
    exact hf

theorem lookup_complete (D C t lambda : ℕ) (hD : 0<D) (hC : 0<C) (ht : t<C)
    (hScale : D*D≤C) (hPower : 8*C=2^lambda) (f : Farey.Fraction) (hDen : f.den≤D) (hInside : Interior C t f.value) :
    ∃ g, (lookup D C t lambda).fraction=some g ∧ g.value=f.value := by
  obtain ⟨k,hk⟩ := interior_regular_convergent D C t hD hScale f hDen hInside
  have hMidpoint : (GeneralPaperBucketGeometry.midpoint C t:ℝ)=(((2*t+1:ℕ):ℝ)/((2*C:ℕ):ℝ)) := by
    simp only [GeneralPaperBucketGeometry.midpoint,Rat.cast_div,Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_one,
      Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
  rw [hMidpoint] at hk
  have hBound : (Real.convergent (((2*t+1:ℕ):ℝ)/((2*C:ℕ):ℝ)) k).den≤D := by
    rw [←hk]
    exact (Farey.value_den_le f).trans hDen
  obtain ⟨g,hg,hError⟩ := bounded_convergent_dominance D C t lambda hD hC ht hPower k hBound
  rw [←hk] at hError
  have hTarget : valueError (2*t+1) (2*C) f.value<1/(2*(C:ℚ)) := by
    rw [midpoint_error]
    exact midpoint_distance C t hC f.value hInside
  have hClose := hError.trans_lt hTarget
  rw [midpoint_error] at hClose
  have hGInside := distance_interior C t hC g.value hClose
  have hGDen := raw_bounded D C t lambda g hg
  refine ⟨g,?_,interiors_equal D C t hD hScale g f hGDen hDen hGInside hInside⟩
  dsimp only [lookup]
  rw [hg]
  simp only [Option.bind_some]
  exact if_pos hGInside

theorem lookup_none_iff_empty (D C t lambda : ℕ) (hD : 0<D) (hC : 0<C) (ht : t<C)
    (hScale : D*D≤C) (hPower : 8*C=2^lambda) :
    (lookup D C t lambda).fraction=none ↔ ∀ f : Farey.Fraction, f.den≤D → ¬Interior C t f.value := by
  constructor
  · intro hNone f hDen hInside
    obtain ⟨g,hSome,_⟩ := lookup_complete D C t lambda hD hC ht hScale hPower f hDen hInside
    rw [hNone] at hSome
    cases hSome
  · exact lookup_none_if_empty D C t lambda

end Blotto.GeneralPaperMidpointComplete
