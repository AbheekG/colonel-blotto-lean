import Blotto.GeneralPaperOrderedDPExecution

/-! The native input proves every leaf profit is at most twice Q_prof.
Weights, reached cached tail bounds and shared zero padding discharge all
premises. The predicate is erased, not a table validation pass. -/
namespace Blotto.GeneralPaperOrderedDPProfitCaps
open GeneralPaperResponseTag GeneralPaperOrderedProfitDP
open GeneralPaperUnsignedCellConstancy (Prefix)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 5000000

def Leaves {K : ℕ} (cap : ℕ) : {h : ℕ} → Tree Tag K h → Prop
  | _,.leaf field => ∀ i,(field.read i).1≤cap
  | _,.node left right => Leaves cap left ∧ Leaves cap right

theorem dummy (K cap : ℕ) : Leaves cap (.leaf (GeneralPaperOrderedProfitTreeBuild.dummy Tag K).1) := by
  intro i
  rw [GeneralPaperOrderedProfitTreeBuild.dummy,FixedArrayTable.read_ofFn]
  exact Nat.zero_le _

theorem build {K : ℕ} (cap height : ℕ) (input : List (GeneralPaperOrderedProfitTreeBuild.WeightedField Tag K))
    (hInput : ∀ field∈input,Leaves cap (.leaf field.1)) : Leaves cap (GeneralPaperOrderedProfitTreeBuild.build height input) := by
  induction height generalizing input with
  | zero =>
    cases input with
    | nil => exact dummy K cap
    | cons field rest => exact hInput field List.mem_cons_self
  | succ height ih =>
    exact ⟨ih _ (fun field hf => hInput field (List.mem_of_mem_take hf)),
      ih _ (fun field hf => hInput field (List.mem_of_mem_drop hf))⟩

theorem padded {K : ℕ} (cap height : ℕ) (input : List (GeneralPaperOrderedProfitTreeBuild.WeightedField Tag K))
    (hInput : ∀ field∈input,Leaves cap (.leaf field.1)) :
    Leaves cap (GeneralPaperOrderedProfitTreeBuild.build height (GeneralPaperOrderedProfitTreeBuild.pad height input)) := by
  apply build cap height
  intro field hf
  rcases List.mem_append.mp hf with hf|hf
  · exact hInput field hf
  · have he := (List.mem_replicate.mp hf).2
    subst field
    exact dummy K cap

theorem native_tree {m k : ℕ} (Qv T : ℕ) (prepared : GeneralPaperProfitParameters.Prepared)
    (ready : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k))
    (hp : prepared=GeneralPaperProfitParameters.prepare m ready.alphabet.lambda k Qv)
    (hT : T=(GeneralPaperTrajectoryParameters.prepare ready.alphabet.lambda k).rows) (hWeights : ∑ j,weights.read j=Qv)
    (hGood : ∀ j,GeneralPaperMeshPrefixInvariant.Good m ready.alphabet.lambda k Qv (prefixes.read j)) :
    Leaves (2*prepared.parameters.qProf) (GeneralPaperOrderedNativeProfitOptimizer.inputTree prepared T weights prefixes ready.cached) := by
  apply padded
  intro field hf
  obtain ⟨j,hj⟩ := List.mem_ofFn.mp hf
  rw [←hj]
  intro i
  have h := GeneralPaperNativeGridQueryPrice.numerator_bound m ready.alphabet.lambda Qv T (weights.read j)
    (prefixes.read j) (ready.cached.read j) i hT (GeneralPaperNativeProfitFieldsPrice.weight_bound weights Qv hWeights j)
    (GeneralPaperActualNativeProfitFields.meshes ready j) (hGood j)
  exact h.trans_eq (by rw [hp]; rfl)

end Blotto.GeneralPaperOrderedDPProfitCaps
