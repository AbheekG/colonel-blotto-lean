import Blotto.GeneralPaperCatalogueGlobalErrors
import Blotto.GeneralPaperFourBlockRegret

/-! Four weighted geometric regrets for the actual own-tree execution.
Both the global increments and the true-loss errors are derived, rather
than supplied independent histories. Values weight the regret once; they
do not multiply the per-field normalized learner updates.
-/
namespace Blotto.GeneralPaperCatalogueGlobalRegret
open scoped BigOperators
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueOccurrenceHistory GeneralPaperCatalogueGlobalLaw
set_option autoImplicit false
set_option maxHeartbeats 3500000

def learner (block : Fin 4) : Learner :=
  match block.val with
  | 0 => .p
  | 1 => .q
  | 2 => .lambda
  | _ => .mu

def size (a : Alphabet) (block : Fin 4) : ℕ := 2^(treeHeight (learner block) a.lambda)

noncomputable def values {m : ℕ} (Qv : ℕ) (weights : FixedArrayTable m ℕ) (j : Fin m) : ℝ := (weights.read j:ℝ)/Qv

theorem values_nonnegative {m : ℕ} (Qv : ℕ) (weights : FixedArrayTable m ℕ) (j : Fin m) : 0≤values Qv weights j := by
  unfold values
  positivity

theorem values_sum {m : ℕ} (Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ) (hWeights : ∑ j, weights.read j=Qv) :
    ∑ j, values Qv weights j=1 := by
  unfold values
  rw [← Finset.sum_div,← Nat.cast_sum,hWeights,div_self (by exact_mod_cast hQv.ne')]

theorem magnitude_cap (block : Fin 4) :
    GeneralPaperCatalogueGlobalHistory.magnitude (learner block)=GeneralPaperFourBlockRegret.cap block := by
  fin_cases block <;> norm_num [learner,GeneralPaperCatalogueGlobalHistory.magnitude,GeneralPaperFourBlockRegret.cap]

theorem size_positive (a : Alphabet) (block : Fin 4) : 0<size a block := Nat.two_pow_pos _

theorem size_bound (a : Alphabet) (block : Fin 4) : size a block≤2^(a.lambda+1) := by
  exact Nat.pow_le_pow_right (by decide) (tree_height_bound (learner block) a.lambda)

noncomputable def averageRegret {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (u : (block : Fin 4) → Fin m → Fin (size a block) → ℝ) : ℝ :=
  (∑ block, GeneralPaperFourBlockRegret.weightedRegret (values Qv weights) (GeneralPaperCachedMassJoin.base k)
    (fun j => history (learner block) (prepare a k Qv weights Bc Br) a k j)
    (fun j time i => GeneralPaperCatalogueGlobalErrors.truth (learner block) a k Qv weights Bc Br time j i)
    (u block) (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows)/
      (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows

theorem average_regret {m : ℕ} (a : Alphabet) (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hWeights : ∑ j, weights.read j=Qv) (Bc Br : ℚ)
    (u : (block : Fin 4) → Fin m → Fin (size a block) → ℝ)
    (hu : ∀ block j i, 0≤u block j i) (hsu : ∀ block j, ∑ i, u block j i=1) :
    averageRegret a k Qv weights Bc Br u≤
      4*((a.lambda:ℝ)+1)/(((GeneralPaperSourceParameters.prepare k).eta:ℝ)*(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows)+
        20*((GeneralPaperSourceParameters.prepare k).eta:ℝ)+8*(49*((GeneralPaperSourceParameters.prepare k).eta:ℝ)/128) := by
  apply GeneralPaperFourBlockRegret.paper_average_regret (size a) (size_positive a) a.lambda (size_bound a)
    (values Qv weights) (values_nonnegative Qv weights) (values_sum Qv hQv weights hWeights)
    (GeneralPaperSourceParameters.prepare k).eta (GeneralPaperSourceParameters.prepare k).theta
    (GeneralPaperSourceParameters.positive k).2.1 (GeneralPaperSourceParameters.positive k).2.2.2 (GeneralPaperSourceParameters.eta_theta k)
    (fun block j => history (learner block) (prepare a k Qv weights Bc Br) a k j) u hu hsu
    (fun block j time i => GeneralPaperCatalogueGlobalErrors.truth (learner block) a k Qv weights Bc Br time j i)
    (49*((GeneralPaperSourceParameters.prepare k).eta:ℝ)/128) _ _ _ (GeneralPaperTrajectoryParameters.rows_positive a.lambda k)
  · intro block j time i
    rw [← magnitude_cap]
    exact GeneralPaperCatalogueGlobalHistory.sharp_magnitude (learner block) a k Qv weights Bc Br time j i.val
  · intro block j time i
    exact GeneralPaperCatalogueGlobalErrors.error_bound (learner block) a k Qv weights Bc Br time j i

theorem regret_with_optimizer_slack {m : ℕ} (a : Alphabet) (k Qv : ℕ) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hWeights : ∑ j, weights.read j=Qv) (Bc Br : ℚ)
    (u : (block : Fin 4) → Fin m → Fin (size a block) → ℝ)
    (hu : ∀ block j i, 0≤u block j i) (hsu : ∀ block j, ∑ i, u block j i=1) :
    averageRegret a k Qv weights Bc Br u+2*(25*((GeneralPaperSourceParameters.prepare k).eta:ℝ)/16)<
      ((GeneralPaperSourceParameters.prepare k).z:ℝ)/64 := by
  have hr := average_regret a k Qv hQv weights hWeights Bc Br u hu hsu
  have hs := GeneralPaperSourceParameters.gamma_source_slack a.lambda k
  have he : 25*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+3*((GeneralPaperSourceParameters.prepare k).theta:ℝ)=
      49*((GeneralPaperSourceParameters.prepare k).eta:ℝ)/128 := by exact_mod_cast GeneralPaperSourceParameters.loss_error k
  have ho : ((GeneralPaperSourceParameters.prepare k).eta:ℝ)+40*((GeneralPaperSourceParameters.prepare k).nu:ℝ)+
      4*((GeneralPaperSourceParameters.prepare k).theta:ℝ)=25*((GeneralPaperSourceParameters.prepare k).eta:ℝ)/16 :=
    by exact_mod_cast GeneralPaperSourceParameters.optimizer_error k
  unfold GeneralPaperSourceParameters.gamma at hs
  rw [he,ho] at hs
  linarith only [hr,hs]

end Blotto.GeneralPaperCatalogueGlobalRegret
