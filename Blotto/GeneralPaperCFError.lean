import Blotto.GeneralPaperCFModel

/-! Exact rational approximation error of actual continuants and monotonicity
along the accepted source loop. The determinant and conserved linear
identities turn the error into the current Euclidean remainder divided by the
original and current denominators. The last accepted selection survives a
rejected lookahead unchanged.
-/
namespace Blotto.GeneralPaperCFError
open GeneralPaperRegularCFLoop GeneralPaperRegularCFFuel GeneralPaperCFLinearInvariant
open GeneralPaperCFDeterminant GeneralPaperCFAdvanceData
set_option autoImplicit false
set_option maxHeartbeats 2500000

def valueError (N M : ℕ) (value : ℚ) : ℚ := |(N:ℚ)/M-value|

def currentError (N M : ℕ) (s : State) : ℚ := valueError N M ((s.previousNum:ℚ)/s.previousDen)

theorem cross_residue (N M : ℕ) (s : State) (hLinear : Linear N M s) (hUnimodular : Unimodular s) :
    |(N:ℚ)*s.previousDen-(M:ℚ)*s.previousNum|=(s.denominator:ℚ) := by
  have hn : (N:ℚ)=(s.numerator:ℚ)*s.previousNum+(s.denominator:ℚ)*s.olderNum := by exact_mod_cast hLinear.1
  have hm : (M:ℚ)=(s.numerator:ℚ)*s.previousDen+(s.denominator:ℚ)*s.olderDen := by exact_mod_cast hLinear.2
  have he : (N:ℚ)*s.previousDen-(M:ℚ)*s.previousNum=
      (s.denominator:ℚ)*((s.olderNum:ℚ)*s.previousDen-(s.olderDen:ℚ)*s.previousNum) := by
    rw [hn,hm]
    ring
  rw [he]
  rcases hUnimodular with h|h
  · have hd : (s.previousNum:ℚ)*s.olderDen=(s.olderNum:ℚ)*s.previousDen+1 := by exact_mod_cast h
    have hh : (s.olderNum:ℚ)*s.previousDen-(s.olderDen:ℚ)*s.previousNum=-1 := by nlinarith only [hd]
    rw [hh,mul_neg_one,abs_neg,abs_of_nonneg (Nat.cast_nonneg _)]
  · have hd : (s.olderNum:ℚ)*s.previousDen=(s.previousNum:ℚ)*s.olderDen+1 := by exact_mod_cast h
    have hh : (s.olderNum:ℚ)*s.previousDen-(s.olderDen:ℚ)*s.previousNum=1 := by nlinarith only [hd]
    rw [hh,mul_one,abs_of_nonneg (Nat.cast_nonneg _)]

theorem current_error_exact (N M : ℕ) (s : State) (hLinear : Linear N M s) (hUnimodular : Unimodular s)
    (hM : 0<M) (hQ : 0<s.previousDen) : currentError N M s=(s.denominator:ℚ)/((M:ℚ)*s.previousDen) := by
  have hm : (0:ℚ)<M := by exact_mod_cast hM
  have hq : (0:ℚ)<s.previousDen := by exact_mod_cast hQ
  unfold currentError valueError
  calc
    _ = |((N:ℚ)*s.previousDen-(M:ℚ)*s.previousNum)/((M:ℚ)*s.previousDen)| := by
      congr 1
      field_simp [hm.ne',hq.ne']
      <;> ring
    _ = _ := by rw [abs_div,abs_of_pos (mul_pos hm hq),cross_residue N M s hLinear hUnimodular]

structure Post (N M width : ℕ) (s : State) : Prop where
  pair : PairBound width s
  linear : Linear N M s
  unimodular : Unimodular s
  order : s.denominator≤s.numerator
  positiveDen : 0<s.previousDen

theorem advance_post (D N M width : ℕ) (s : State) (h : Post N M width s) : Post N M width (advance D (width+2) s).1 := by
  exact ⟨advance_pair_bound D width s h.pair,advance_linear D width N M s h.pair h.linear,
    advance_unimodular D (width+2) s h.unimodular,euclidean_order D width s h.pair h.order,
    h.positiveDen.trans_le (previous_den_mono D width s h.pair h.order)⟩

theorem advance_error (D N M width : ℕ) (s : State) (hM : 0<M) (h : Post N M width s) :
    currentError N M (advance D (width+2) s).1≤currentError N M s := by
  by_cases hz : s.denominator=0
  · simp [advance,hz,currentError,valueError]
  · have hd : 0<s.denominator := by omega
    have hn := advance_post D N M width s h
    have hm : (0:ℚ)<M := by exact_mod_cast hM
    have hq : (0:ℚ)<s.previousDen := by exact_mod_cast h.positiveDen
    have hqn : (0:ℚ)<(advance D (width+2) s).1.previousDen := by exact_mod_cast hn.positiveDen
    have he := advance_euclidean D (width+2) s hd (quotient_cap width _ _ h.pair.1 hd)
    have hr : (advance D (width+2) s).1.denominator≤s.denominator := by rw [he.2]; exact (Nat.mod_lt _ hd).le
    have hrq : ((advance D (width+2) s).1.denominator:ℚ)≤s.denominator := by exact_mod_cast hr
    have hmq : (s.previousDen:ℚ)≤(advance D (width+2) s).1.previousDen := by
      exact_mod_cast previous_den_mono D width s h.pair h.order
    rw [current_error_exact N M s h.linear h.unimodular hM h.positiveDen,
      current_error_exact N M _ hn.linear hn.unimodular hM hn.positiveDen]
    exact (div_le_div_of_nonneg_right hrq (mul_pos hm hqn).le).trans
      (div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos hm hq) (mul_le_mul_of_nonneg_left hmq hm.le))

def CurrentSelected (s : State) : Prop :=
  ∃ f, s.selected=some f ∧ f.num=s.previousNum ∧ f.den=s.previousDen

theorem selected_error (N M : ℕ) (s : State) (f : Farey.Fraction) (hNum : f.num=s.previousNum) (hDen : f.den=s.previousDen) :
    valueError N M f.value=currentError N M s := by
  simp only [currentError,valueError,Farey.Fraction.value,hNum,hDen]

theorem run_selected_dominance (D N M width fuel : ℕ) (s : State) (hM : 0<M) (h : Post N M width s)
    (hSelected : CurrentSelected s) :
    ∃ f, (run D (width+2) fuel s).selected=some f ∧ valueError N M f.value≤currentError N M s := by
  induction fuel generalizing s with
  | zero =>
    obtain ⟨f,hf,hp,hq⟩ := hSelected
    exact ⟨f,hf,(selected_error N M s f hp hq).le⟩
  | succ fuel ih =>
    cases hb : (advance D (width+2) s).2 with
    | false =>
      obtain ⟨f,hf,hp,hq⟩ := hSelected
      refine ⟨f,?_,(selected_error N M s f hp hq).le⟩
      simp only [run,hb,Bool.false_eq_true,ite_false,stopped_selection D (width+2) s hb,hf]
    | true =>
      have hn := advance_post D N M width s h
      have hs : CurrentSelected (advance D (width+2) s).1 := continuing_selection D (width+2) s hb
      obtain ⟨f,hf,he⟩ := ih _ hn hs
      exact ⟨f,by simpa only [run,hb,ite_true] using hf,he.trans (advance_error D N M width s hM h)⟩

end Blotto.GeneralPaperCFError
