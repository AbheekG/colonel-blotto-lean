import Blotto.PlayerSpecificRationalRootDenominator

/-! Every rational root of a nonzero degree-at-most-three input has a
denominator bounded by a dyadic integer computed from its actual encoding.
The proof covers all signs and handles trailing coefficient zeros. -/
namespace Blotto.PlayerSpecificRationalRootBound
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificIntegerPolynomial
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem dense_divisibility (p : List ℤ) (hlen : p.length≤4) (q : ℚ)
    (hr : evaluate (p.map (fun (a : ℤ) => (a:ℚ))) q=0) : q.den∣(p.getLast?.getD 0).natAbs := by
  cases p with
  | nil => exact Nat.dvd_zero _
  | cons a0 p =>
    cases p with
    | nil =>
      have he : (a0:ℚ)=0 := by
        simpa only [List.map_cons,List.map_nil,evaluate,List.foldr_cons,List.foldr_nil,mul_zero,add_zero] using hr
      have hz : a0=0 := by exact_mod_cast he
      change q.den∣a0.natAbs
      rw [hz,Int.natAbs_zero]
      exact Nat.dvd_zero _
    | cons a1 p =>
      cases p with
      | nil =>
        change q.den∣a1.natAbs
        apply PlayerSpecificRationalRootDenominator.linear q a0 a1
        simpa only [List.map_cons,List.map_nil,evaluate,List.foldr_cons,List.foldr_nil,mul_zero,add_zero] using hr
      | cons a2 p =>
        cases p with
        | nil =>
          change q.den∣a2.natAbs
          apply PlayerSpecificRationalRootDenominator.quadratic q a0 a1 a2
          simpa only [List.map_cons,List.map_nil,evaluate,List.foldr_cons,List.foldr_nil,mul_zero,add_zero] using hr
        | cons a3 p =>
          cases p with
          | nil =>
            change q.den∣a3.natAbs
            apply PlayerSpecificRationalRootDenominator.cubic q a0 a1 a2 a3
            simpa only [List.map_cons,List.map_nil,evaluate,List.foldr_cons,List.foldr_nil,mul_zero,add_zero] using hr
          | cons a4 p => simp only [List.length_cons] at hlen; omega

def denominatorCap (p : Data) : ℕ := 2^(5*PlayerSpecificRationalMagnitude.inputHeight p)

theorem denominator_lt (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) (q : ℚ) (hq : evaluate p q=0) :
    q.den<denominatorCap p := by
  let normalized:=trim p
  let cleared:=clear normalized
  let leading:ℤ:=cleared.getLast?.getD 0
  have hnorm:=PlayerSpecificPolynomialNormalization.trim_normalized p
  have hn : normalized≠[] := fun hz => hp ((PlayerSpecificPolynomialNormalization.trim_nil_iff p).mp hz)
  have hlenNorm : normalized.length≤4 := (trim_length p).trans hlen
  have hlenClear : cleared.length≤4 := (length normalized).trans_le hlenNorm
  have hclear : cleared≠[] := by
    intro hz
    have he:=length normalized
    change cleared.length=normalized.length at he
    rw [hz,List.length_nil] at he
    exact hn (List.length_eq_zero_iff.mp he.symm)
  have hleading : leading≠0 := leading_nonzero normalized hnorm hn
  have hroot : evaluate normalized q=0 := by
    rw [←evaluate_semantics,trim_semantics,evaluate_semantics]
    exact hq
  have hcleared : evaluate (cleared.map (fun (a : ℤ) => (a:ℚ))) q=0 := (roots normalized q).mpr hroot
  have hd : q.den∣leading.natAbs := dense_divisibility cleared hlenClear q hcleared
  have hpos : 0<leading.natAbs := Int.natAbs_pos.mpr hleading
  have hle : q.den≤leading.natAbs := Nat.le_of_dvd hpos hd
  have hmem : leading∈cleared := by
    unfold leading
    rw [List.getLast?_eq_some_getLast hclear,Option.getD_some]
    exact List.mem_of_getLast? (List.getLast?_eq_some_getLast hclear)
  have hcoef:=coefficient_bound normalized (PlayerSpecificRationalMagnitude.inputHeight p)
    (trim_height (input_height p)) hlenNorm leading hmem
  exact hle.trans_lt hcoef

end Blotto.PlayerSpecificRationalRootBound
