import Blotto.GeneralPaperCFReference

/-! A proof-only forward observer of Euclidean continuant updates. Primitive
Nat division/modulus in this observer specify the arithmetic loop's results;
they are not used by the executed midpoint query. The forward matrix update
agrees with the recursive rational reference for every convergent index.
-/
namespace Blotto.GeneralPaperCFModel
open GeneralPaperRegularCFLoop GeneralPaperRegularCFFuel
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Core where
  numerator : ℕ
  denominator : ℕ
  olderNum : ℕ
  olderDen : ℕ
  previousNum : ℕ
  previousDen : ℕ
  deriving DecidableEq

def view (s : State) : Core := ⟨s.numerator,s.denominator,s.olderNum,s.olderDen,s.previousNum,s.previousDen⟩

def initial (n d : ℕ) : Core := ⟨n,d,0,1,1,0⟩

def step (s : Core) : Core :=
  if s.denominator=0 then s else
    ⟨s.denominator,s.numerator%s.denominator,s.previousNum,s.previousDen,
      (s.numerator/s.denominator)*s.previousNum+s.olderNum,(s.numerator/s.denominator)*s.previousDen+s.olderDen⟩

def iterate : ℕ → Core → Core
  | 0,s => s
  | k+1,s => iterate k (step s)

def future (s : Core) (k : ℕ) : ℕ × ℕ := ((iterate (k+1) s).previousNum,(iterate (k+1) s).previousDen)

theorem iterate_zero_denominator (k : ℕ) (s : Core) (hd : s.denominator=0) : iterate k s=s := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [iterate,step,ite_eq_left hd] using ih

theorem future_zero_denominator (s : Core) (k : ℕ) (hd : s.denominator=0) : future s k=(s.previousNum,s.previousDen) := by
  rw [future,iterate_zero_denominator _ s hd]

theorem future_succ (s : Core) (k : ℕ) : future s (k+1)=future (step s) k := rfl

theorem forward_reference (s : Core) (k : ℕ) (hd : 0<s.denominator) :
    (future s k).1=(GeneralPaperCFReference.pair s.numerator s.denominator k).1*s.previousNum+
        (GeneralPaperCFReference.pair s.numerator s.denominator k).2*s.olderNum ∧
      (future s k).2=(GeneralPaperCFReference.pair s.numerator s.denominator k).1*s.previousDen+
        (GeneralPaperCFReference.pair s.numerator s.denominator k).2*s.olderDen := by
  induction k generalizing s with
  | zero =>
    simp only [future,iterate,step,ite_eq_right hd.ne',GeneralPaperCFReference.pair,Nat.one_mul,and_self]
  | succ k ih =>
    by_cases hr : s.numerator%s.denominator=0
    · have hz : (step s).denominator=0 := by simp only [step,ite_eq_right hd.ne',hr]
      rw [future_succ,future_zero_denominator _ _ hz]
      simp only [GeneralPaperCFReference.pair,ite_eq_left hr,step,ite_eq_right hd.ne',Nat.one_mul,and_self]
    · have hp : 0<(step s).denominator := by
        simp only [step,ite_eq_right hd.ne']
        omega
      have hh := ih (step s) hp
      rw [future_succ,hh.1,hh.2]
      simp only [GeneralPaperCFReference.pair,ite_eq_right hr,step,ite_eq_right hd.ne']
      constructor <;> ring

theorem initial_future (n d k : ℕ) (hd : 0<d) : future (initial n d) k=GeneralPaperCFReference.pair n d k := by
  obtain ⟨hn,hq⟩ := forward_reference (initial n d) k hd
  apply Prod.ext
  · simpa only [initial,Nat.mul_one,Nat.mul_zero,Nat.add_zero] using hn
  · simpa only [initial,Nat.mul_one,Nat.mul_zero,Nat.zero_add] using hq

theorem initial_value_eq_regular (n d k : ℕ) (hd : 0<d) :
    ((future (initial n d) k).1:ℚ)/(future (initial n d) k).2=Real.convergent ((n:ℝ)/d) k := by
  rw [initial_future n d k hd]
  exact GeneralPaperCFReference.value_eq_regular n d k hd

theorem advance_view (D width : ℕ) (s : State) (hPair : PairBound width s) :
    view (advance D (width+2) s).1=step (view s) := by
  by_cases hz : s.denominator=0
  · simp [advance,view,step,hz]
  · have hd : 0<s.denominator := by omega
    have hc := quotient_cap width _ _ hPair.1 hd
    have hq := GeneralPaperConstructedNatDivision.quotient_eq s.numerator s.denominator (width+2) hd hc
    have hr := GeneralPaperConstructedNatDivision.remainder_eq s.numerator s.denominator (width+2) hd hc
    simp only [advance,ite_eq_right hz,view,step,hq,hr]
    split
    · split <;> simp [hz]
    · simp [hz]

end Blotto.GeneralPaperCFModel
