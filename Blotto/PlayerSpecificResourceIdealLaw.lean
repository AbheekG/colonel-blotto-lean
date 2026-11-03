import Blotto.PlayerSpecificResourceIdealLeaves
import Blotto.PlayerSpecificFairAveraging
import Blotto.BinaryMixture

/-! Exact-probability whole-output semantics follows the executing
resource requests and updates. It is a proof-only finite recursion with
an arbitrary terminal allocation law, not a runtime execution tree. -/
namespace Blotto.PlayerSpecificResourceIdealLaw
open MeasureTheory PlayerSpecificDensePolynomial PlayerSpecificSturmVariations
open PlayerSpecificAlgebraicResourceState PlayerSpecificAlgebraicResourceRequest
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem event_bounds {M : ℕ} (l : Mixed M) (A : Set (Allocation M)) :
    0 ≤ (l : Measure (Allocation M)).real A ∧ (l : Measure (Allocation M)).real A ≤ 1 := by
  refine ⟨measureReal_nonneg,?_⟩
  simpa only [probReal_univ] using (measureReal_mono (μ := (l : Measure (Allocation M))) (Set.subset_univ A))

theorem binary_event {M : ℕ} (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) (u l : Mixed M)
    (A : Set (Allocation M)) (hA : MeasurableSet A) :
    (binaryLaw q hq u l : Measure (Allocation M)).real A=
      q*(u : Measure (Allocation M)).real A+(1-q)*(l : Measure (Allocation M)).real A := by
  rw [binaryLaw,probabilityMixture_real_apply _ _ _ _ _ hA]
  simp [Fin.sum_univ_succ]

noncomputable def law {N M : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (x : ℝ)
    (leaf : State N → Mixed M) : (C : ℕ) → (s : State N) → PlayerSpecificResourceIdealMean.Normalized model p x C s → Mixed M
  | 0,s,_ => leaf s
  | C+1,s,hn => match he : request model p s with
      | none => leaf s
      | some frame => binaryLaw (realEvaluate frame.pair.probability x) (hn frame he).1
          (law model p x leaf C (advance model p s frame true) (hn frame he).2.1)
          (law model p x leaf C (advance model p s frame false) (hn frame he).2.2)

theorem event {N M : ℕ} (model : RationalCostModel) (p : PlayerSpecificAlgebraicInitialVector.Result N) (x : ℝ)
    (leaf : State N → Mixed M) (C : ℕ) (s : State N) (hn : PlayerSpecificResourceIdealMean.Normalized model p x C s)
    (A : Set (Allocation M)) (hA : MeasurableSet A) :
    (law model p x leaf C s hn : Measure (Allocation M)).real A=
      PlayerSpecificResourceIdealMean.mean model p x (fun t => (leaf t : Measure (Allocation M)).real A) C s := by
  induction C generalizing s with
  | zero => rfl
  | succ C ih =>
    rw [law]
    split
    · rename_i he
      simp only [PlayerSpecificResourceIdealMean.mean,he]
    · rename_i frame he
      rw [binary_event _ _ _ _ A hA,ih,ih]
      simp only [PlayerSpecificResourceIdealMean.mean,he]

end Blotto.PlayerSpecificResourceIdealLaw
