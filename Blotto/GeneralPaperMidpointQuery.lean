import Blotto.GeneralPaperRegularCFFuel

/-! Actual selected midpoint query: arithmetic Euclidean quotients, regular
continuant recurrence, last bounded denominator and both strict endpoint
checks. Returned values are sound and unique; constructed fuel reaches an
actual stopping branch. Completeness still needs the loop's regular-CF
coverage join to the checked Legendre criterion, and full query bit/space
and amortized real work remain required.
-/
namespace Blotto.GeneralPaperMidpointQuery
open GeneralPaperBucketGeometry GeneralPaperRegularCFLoop GeneralPaperRegularCFFuel
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Result where
  fraction : Option Farey.Fraction
  work : ℕ
  steps : ℕ
  quotientDepth : ℕ

def raw (D C t lambda : ℕ) : State := run D (lambda+2) (2*lambda+4) (initial C t)

def lookup (D C t lambda : ℕ) : Result :=
  let finished := raw D C t lambda
  let checked := finished.selected.bind (fun f => if lower C t<f.value ∧ f.value<upper C t then some f else none)
  ⟨checked,finished.work+32,finished.steps,finished.quotientDepth⟩

theorem raw_bounded (D C t lambda : ℕ) : SelectedBounded D (raw D C t lambda) :=
  run_selected_bounded D (lambda+2) (2*lambda+4) (initial C t) (initial_bounded D C t)

theorem lookup_sound (D C t lambda : ℕ) (f : Farey.Fraction) (hSome : (lookup D C t lambda).fraction=some f) :
    f.den≤D ∧ Interior C t f.value := by
  have hBound := raw_bounded D C t lambda
  dsimp only [lookup] at hSome
  cases hs : (raw D C t lambda).selected with
  | none => simp only [hs,Option.bind_none,reduceCtorEq] at hSome
  | some chosen =>
    simp only [hs,Option.bind_some] at hSome
    split at hSome
    · rename_i hInside
      have he := Option.some.inj hSome
      subst f
      exact ⟨hBound chosen hs,hInside⟩
    · cases hSome

theorem lookup_none_if_empty (D C t lambda : ℕ) (hEmpty : ∀ f : Farey.Fraction, f.den≤D → ¬Interior C t f.value) :
    (lookup D C t lambda).fraction=none := by
  cases hs : (lookup D C t lambda).fraction with
  | none => rfl
  | some f =>
    have he := lookup_sound D C t lambda f hs
    exact (hEmpty f he.1 he.2).elim

theorem lookup_unique (D C t lambda : ℕ) (hD : 0<D) (hScale : D*D≤C)
    (f : Farey.Fraction) (hSome : (lookup D C t lambda).fraction=some f)
    (other : Farey.Fraction) (hOther : other.den≤D) (hInterior : Interior C t other.value) : f.value=other.value := by
  have he := lookup_sound D C t lambda f hSome
  exact interiors_equal D C t hD hScale f other he.1 hOther he.2 hInterior

theorem lookup_unit (D C t lambda : ℕ) (hC : 0<C) (ht : t<C)
    (f : Farey.Fraction) (hSome : (lookup D C t lambda).fraction=some f) : 0≤f.value ∧ f.value<1 := by
  have he := lookup_sound D C t lambda f hSome
  have hUpper : upper C t≤1 := by
    unfold upper
    apply (div_le_one (show (0:ℚ)<C by exact_mod_cast hC)).mpr
    exact_mod_cast (show t+1≤C by omega)
  exact ⟨Farey.value_nonnegative f,he.2.2.trans_le hUpper⟩

theorem lookup_closed_denominator (D C t lambda : ℕ) (hD : 0<D) (hScale : D*D≤C)
    (f : Farey.Fraction) (hSome : (lookup D C t lambda).fraction=some f) : f.den≤C := by
  have hd : D≤D*D := by
    have he := Nat.mul_le_mul_left D (show 1≤D by omega)
    simpa only [Nat.mul_one] using he
  exact (lookup_sound D C t lambda f hSome).1.trans (hd.trans hScale)

theorem midpoint_actual_stop (D C t lambda : ℕ) (hC : 0<C) (ht : t<C) (hPower : 8*C=2^lambda) :
    ∃ last, (advance D (lambda+2) last).2=false ∧ raw D C t lambda=(advance D (lambda+2) last).1 :=
  stopped_result D (lambda+2) (2*lambda+4) (initial C t) (midpoint_stops D C t lambda hC ht hPower)

theorem lookup_work_counter (D C t lambda : ℕ) :
    (lookup D C t lambda).work≤14*(lookup D C t lambda).quotientDepth+64*(lookup D C t lambda).steps+44 := by
  have he := initial_work D (lambda+2) (2*lambda+4) C t
  dsimp only [lookup,raw]
  omega

end Blotto.GeneralPaperMidpointQuery
