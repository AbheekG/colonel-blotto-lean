import Blotto.RationalRecursiveProposalKernel

/-! Recursive bounded-test error immediately controls every record event and
any total postprocessing map. Repeated independent draws add, rather than
condition, the errors; identity to a concrete finite layout remains separate. -/

namespace Blotto
open scoped Classical
namespace RationalWeightedGuideTree

theorem proposalKernel_event_error (tree : RationalWeightedGuideTree) (B : ℚ) (K : ℕ)
    (event : Set (Option tree.Record)) :
    |(tree.proposalKernel true B K).mean (fun record => if record ∈ event then 1 else 0) -
      (tree.proposalKernel false B K).mean (fun record => if record ∈ event then 1 else 0)| ≤
        (tree.nodes : ℝ) * (1 / (2 : ℝ) ^ K) := by
  apply tree.proposalKernel_error B K
  intro record
  split_ifs <;> norm_num

theorem proposalKernel_map_error {α : Type*} (tree : RationalWeightedGuideTree) (B : ℚ) (K : ℕ)
    (post : Option tree.Record → α) :
    ((tree.proposalKernel true B K).map post).Close ((tree.proposalKernel false B K).map post)
      ((tree.nodes : ℝ) * (1 / (2 : ℝ) ^ K)) :=
  BoundedExpectationKernel.map_close _ _ post _ (tree.proposalKernel_error B K)

end RationalWeightedGuideTree
namespace BoundedExpectationKernel

noncomputable def repeated {α : Type*} (k : BoundedExpectationKernel α) : ℕ → BoundedExpectationKernel (List α)
  | 0 => point []
  | n + 1 => k.bind (fun x => (k.repeated n).map (fun tail => x :: tail))

theorem repeat_close {α : Type*} (a b : BoundedExpectationKernel α) (error : ℝ)
    (h : a.Close b error) (n : ℕ) : (a.repeated n).Close (b.repeated n) ((n : ℝ) * error) := by
  induction n with
  | zero => intro f _hf; simp only [repeated, sub_self, abs_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ n ih =>
    have he := bind_close a b (fun x => (a.repeated n).map (fun tail => x :: tail))
      (fun x => (b.repeated n).map (fun tail => x :: tail)) error ((n : ℝ) * error) h
      (fun x => map_close _ _ _ _ ih)
    intro f hf
    have ht := he f hf
    simpa only [repeated, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using ht

end BoundedExpectationKernel
end Blotto
