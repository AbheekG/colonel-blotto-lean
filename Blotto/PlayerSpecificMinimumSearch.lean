import Blotto.PlayerSpecificMinimumTest

/-! Bounded halving search, with an actual rational division on every
failed test and an explicit source work counter. The final guard is proved
sufficient for accepted inputs by the computed positive-length bound. -/
namespace Blotto.PlayerSpecificMinimumSearch
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations
open PlayerSpecificRationalTrace PlayerSpecificAlgebraicReduction PlayerSpecificIsolationState
open PlayerSpecificPositiveFieldLowerBound
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Result where
  quantum : ℚ
  exponent : ℕ
  checks : ℕ
  work : ℕ

def frame (rows : List Data) (fuel s : ℕ) (q : ℚ) : Trace :=
  copyRow [q]++[.control rows.length,.control fuel,.control s]

def search (model : RationalCostModel) (m : Data) (node : Interval) (rows : List Data) : ℕ → ℕ → ℚ → Result
  | 0,s,q =>
    let tested:=PlayerSpecificMinimumTest.all model m node q rows
    ⟨q,s,1,tested.2+price model (frame rows 0 s q)⟩
  | fuel+1,s,q =>
    let tested:=PlayerSpecificMinimumTest.all model m node q rows
    if tested.1 then ⟨q,s,1,tested.2+price model (frame rows (fuel+1) s q)⟩
    else
      let half:=scalar .divide q 2
      let next:=search model m node rows fuel (s+1) half.1
      ⟨next.quantum,next.exponent,next.checks+1,
        tested.2+price model half.2+next.work+price model (frame rows (fuel+1) s q)+
          price model (copyRow [next.quantum]++[.control next.exponent,.control next.checks])⟩

theorem dyadic_succ (s : ℕ) : dyadic (s+1)=dyadic s/2 := by
  unfold dyadic
  rw [pow_succ,div_mul_eq_div_div]

theorem dyadic_antitone : Antitone dyadic := by
  intro a b hab
  unfold dyadic
  exact one_div_le_one_div_of_le (pow_pos (by norm_num) _) (pow_le_pow_right₀ (by norm_num) hab)

theorem search_sound (model : RationalCostModel) (m : Data) (node : Interval) (rows : List Data)
    (hm : Normalized m) (hirr : Irreducible (semantics m)) (hv : node.lo<node.hi)
    (x : ℝ) (hx : PlayerSpecificSelectedRefinement.Unique m node x) (fuel s : ℕ) (q : ℚ)
    (hq : q=dyadic s) (hfinal : ∀ a∈rows,((dyadic (s+fuel)):ℝ)≤realEvaluate a x) :
    let result:=search model m node rows fuel s q
    result.quantum=dyadic result.exponent ∧ s≤result.exponent ∧ result.exponent≤s+fuel ∧
      result.checks≤fuel+1 ∧ 0<result.quantum ∧ ∀ a∈rows,(result.quantum:ℝ)≤realEvaluate a x := by
  induction fuel generalizing s q with
  | zero =>
    simp only [search,Nat.add_zero] at hfinal ⊢
    exact ⟨hq,le_rfl,le_rfl,le_rfl,hq.symm ▸ dyadic_positive s,by simpa only [hq] using hfinal⟩
  | succ fuel ih =>
    simp only [search]
    split
    · rename_i hpass
      have hall:=(PlayerSpecificMinimumTest.all_correct model m node q rows hm hirr hv x hx).mp hpass
      dsimp only
      exact ⟨hq,le_rfl,by omega,by omega,hq.symm ▸ dyadic_positive s,hall⟩
    · have hh : (scalar .divide q 2).1=dyadic (s+1) := by
        simp only [scalar,Arithmetic.apply,hq,dyadic_succ]
      have hf : ∀ a∈rows,((dyadic (s+1+fuel)):ℝ)≤realEvaluate a x := by
        simpa only [Nat.add_assoc,Nat.add_comm 1 fuel] using hfinal
      have hn:=ih (s+1) (scalar .divide q 2).1 hh hf
      dsimp only
      exact ⟨hn.1,by omega,by omega,by omega,hn.2.2.2.2.1,hn.2.2.2.2.2⟩

end Blotto.PlayerSpecificMinimumSearch
