import Blotto.FreshBitSeedLifetime
import Blotto.FairBitKernelBlocks

/-! Semantics in the named unit fresh-independent-fair-Boolean primitive
model. Every reached fresh call binds a new fair bit. No fairness or independence
certificate is accepted from a caller. The recursive semantics denotes the
actual accumulator/reversal loop, not an exponentially materialized tree. -/
namespace Blotto.FreshBitSeedKernel
open MeasureTheory
open FreshBitSeedLifetime

noncomputable def fresh : BoundedExpectationKernel Bool where
  mean := fun f => (1/2:ℝ)*f false+(1/2:ℝ)*f true
  constant := by intro c; ring
  monotone := by intro f g h; have hf := h false; have ht := h true; linarith
  add := by intro f g; ring

noncomputable def loop : ℕ → List Bool → BoundedExpectationKernel (List Bool)
  | 0, reversed => BoundedExpectationKernel.point reversed.reverse
  | count+1, reversed => fresh.bind (fun bit => loop count (bit::reversed))

noncomputable def generate (count : ℕ) : BoundedExpectationKernel (List Bool) := loop count []

theorem loop_mean (count : ℕ) (reversed : List Bool) (f : List Bool → ℝ) :
    (loop count reversed).mean f =
      (fairBitKernel count).mean (fun bits => f (reversed.reverse++List.ofFn bits)) := by
  induction count generalizing reversed with
  | zero =>
      simp [loop,BoundedExpectationKernel.point,fairBitKernel,fairBitLaw,booleanVectorPointLaw]
  | succ count ih =>
      change (1/2:ℝ)*(loop count (false::reversed)).mean f+
        (1/2:ℝ)*(loop count (true::reversed)).mean f = _
      rw [ih,ih]
      change _ = ∫ bits, f (reversed.reverse++List.ofFn bits) ∂(fairBitLaw (count+1) : Measure (Fin (count+1) → Bool))
      rw [fairBitLaw_integral_split]
      simp only [List.reverse_cons,List.append_assoc,List.singleton_append,List.ofFn_succ,
        prependBit,Fin.cons_zero,Fin.cons_succ]
      rfl

theorem generate_mean (count : ℕ) (f : List Bool → ℝ) :
    (generate count).mean f = (fairBitKernel count).mean (fun bits => f (List.ofFn bits)) := by
  simpa only [generate,List.reverse_nil,List.nil_append] using loop_mean count [] f

theorem generate_operational (count : ℕ) (f : List Bool → ℝ) :
    (generate count).mean f = (fairBitKernel count).mean
      (fun bits => f (generateWithTrace (tapeFresh (vectorTape bits)) count 0).1.1) := by
  simp only [generate_vector,generate_mean]

noncomputable def pair (R S : ℕ) : BoundedExpectationKernel (List Bool × List Bool) :=
  (generate R).bind (fun first => (generate S).map (fun second => (first,second)))

theorem pair_mean (R S : ℕ) (f : List Bool × List Bool → ℝ) :
    (pair R S).mean f = (fairBitKernel (R+S)).mean
      (fun bits => f (List.ofFn (firstBitBlock R S bits),List.ofFn (secondBitBlock R S bits))) := by
  simp only [pair,BoundedExpectationKernel.bind,BoundedExpectationKernel.map,BoundedExpectationKernel.point]
  rw [generate_mean]
  simp_rw [generate_mean]
  exact (fairBitKernel_blocks R S (fun first second => f (List.ofFn first,List.ofFn second))).symm

-- All joint tests, rather than only marginal means, identify the product law.
theorem pair_product (R S : ℕ) (f : List Bool × List Bool → ℝ) :
    (pair R S).mean f =
      (generate R).mean (fun first => (generate S).mean (fun second => f (first,second))) := rfl

end Blotto.FreshBitSeedKernel
