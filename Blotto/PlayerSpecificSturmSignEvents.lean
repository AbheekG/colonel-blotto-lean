import Blotto.PlayerSpecificSquarefreeAlgorithm
import Mathlib.Topology.Algebra.Polynomial

/-! Local sign behaviour used in the Sturm counting proof: nonzero rows
keep their signs nearby, and a simple root crosses from the opposite sign
of the derivative to its same sign. No root approximation is assumed. -/
namespace Blotto.PlayerSpecificSturmSignEvents
open SignType Filter
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem continuous_sign_near (f : ℝ → ℝ) (a : ℝ) (hf : ContinuousAt f a) (h0 : f a≠0) :
    ∀ᶠ x in 𝓝 a,sign (f x)=sign (f a) := by
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · have h := hf.tendsto.eventually (Iio_mem_nhds hneg)
    exact h.mono (fun x hx => by rw [sign_neg hx,sign_neg hneg])
  · have h := hf.tendsto.eventually (Ioi_mem_nhds hpos)
    exact h.mono (fun x hx => by rw [sign_pos hx,sign_pos hpos])

theorem polynomial_sign_near (p : Polynomial ℝ) (a : ℝ) (h0 : p.eval a≠0) :
    ∀ᶠ x in 𝓝 a,sign (p.eval x)=sign (p.eval a) :=
  continuous_sign_near (fun x => p.eval x) a p.continuousAt h0

theorem root_linear_factor (p : Polynomial ℝ) (a : ℝ) (ha : p.IsRoot a) :
    ∃ q : Polynomial ℝ,p=(Polynomial.X-Polynomial.C a)*q ∧ q.eval a=p.derivative.eval a := by
  rcases Polynomial.dvd_iff_isRoot.mpr ha with ⟨q,hq⟩
  refine ⟨q,hq,?_⟩
  simp only [hq,Polynomial.derivative_mul,Polynomial.derivative_X_sub_C,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,
    sub_self,one_mul,zero_mul,add_zero]

theorem simple_root_sign (p : Polynomial ℝ) (a : ℝ) (ha : p.IsRoot a) (hd : p.derivative.eval a≠0) :
    ∀ᶠ x in 𝓝 a,sign (p.eval x)=sign (x-a)*sign (p.derivative.eval a) := by
  rcases root_linear_factor p a ha with ⟨q,hq,hderiv⟩
  have hq0 : q.eval a≠0 := by rw [hderiv]; exact hd
  have hs := polynomial_sign_near q a hq0
  filter_upwards [hs] with x hx
  calc
    sign (p.eval x)=sign (x-a)*sign (q.eval x) := by
      rw [hq,Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,sign_mul]
    _ = _ := by rw [hx,hderiv]

theorem simple_crossing (p : Polynomial ℝ) (a : ℝ) (ha : p.IsRoot a) (hd : p.derivative.eval a≠0) :
    ∀ᶠ x in 𝓝 a,p.derivative.eval x≠0 ∧
      (x<a → sign (p.eval x) = -sign (p.derivative.eval x)) ∧
      (a<x → sign (p.eval x)=sign (p.derivative.eval x)) := by
  have hs := simple_root_sign p a ha hd
  have hds := polynomial_sign_near p.derivative a hd
  filter_upwards [hs,hds] with x hx hdx
  have hn : p.derivative.eval x≠0 := by
    intro hz
    rw [hz,sign_zero] at hdx
    exact hd (sign_eq_zero_iff.mp hdx.symm)
  refine ⟨hn,?_,?_⟩
  · intro hxa
    rw [hx,sign_neg (sub_neg.mpr hxa),hdx,neg_one_mul]
  · intro hax
    rw [hx,sign_pos (sub_pos.mpr hax),hdx,one_mul]

end Blotto.PlayerSpecificSturmSignEvents
