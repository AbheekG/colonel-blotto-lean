import Blotto.GeneralPaperOrderedTableHeight
import Blotto.GeneralPaperOrderedProfitSound
import Blotto.GeneralPaperSelectedProfitTreePrice

/-! Every actual retained DP cost has its own subtree-height bound. Base
heights come from the native Ready catalogue, including shared zero padding.
No supplied state-validity or height oracle enters execution. -/
namespace Blotto.GeneralPaperOrderedDPHeight
open GeneralPaperResponseTag GeneralPaperOrderedMinimum GeneralPaperOrderedProfitScatter GeneralPaperOrderedProfitDP
set_option autoImplicit false
set_option maxHeartbeats 6000000

def Leaves {K : ℕ} (s : ℕ) : {h : ℕ} → Tree Tag K h → Prop
  | _,.leaf field => ∀ i,RationalHeight (field.read i).2.threshold s
  | _,.node left right => Leaves s left ∧ Leaves s right

theorem states {K q w B h : ℕ} (grid : GeneralPaperProfitGridPrepare.Prepared q w B) (tree : Tree Tag K h)
    (s : ℕ) (hLeaves : Leaves s tree) :
    GeneralPaperOrderedTableHeight.Safe (expressionHeightBudget s h) (run grid tree).table := by
  induction tree with
  | leaf field =>
    intro i chosen hRead
    obtain ⟨a,hChosen,_⟩ := leaf_description grid field i chosen hRead
    subst chosen
    simpa only [expressionHeightBudget_zero] using hLeaves a
  | @node h left right ihl ihr =>
    intro label chosen hRead
    obtain ⟨i,j,a,b,hl,hr,hChosen,_⟩ := merge_description grid (run grid left).table (run grid right).table label chosen hRead
    subst chosen
    exact GeneralPaperTagHeight.add_height s h a.cost b.cost (ihl hLeaves.1 i a hl) (ihr hLeaves.2 j b hr)

theorem dummy_leaves (K s : ℕ) (hs : 0<s) :
    Leaves s (.leaf (GeneralPaperOrderedProfitTreeBuild.dummy Tag K).1) := by
  intro i
  rw [GeneralPaperOrderedProfitTreeBuild.dummy,FixedArrayTable.read_ofFn]
  exact GeneralPaperTagHeight.zero_height s hs

theorem build_leaves {K : ℕ} (s height : ℕ) (hs : 0<s)
    (input : List (GeneralPaperOrderedProfitTreeBuild.WeightedField Tag K))
    (hInput : ∀ field∈input,Leaves s (.leaf field.1)) :
    Leaves s (GeneralPaperOrderedProfitTreeBuild.build height input) := by
  induction height generalizing input with
  | zero =>
    cases input with
    | nil => exact dummy_leaves K s hs
    | cons field rest => exact hInput field List.mem_cons_self
  | succ height ih =>
    exact ⟨ih _ (fun field hf => hInput field (List.mem_of_mem_take hf)),
      ih _ (fun field hf => hInput field (List.mem_of_mem_drop hf))⟩

theorem padded_leaves {K : ℕ} (s height : ℕ) (hs : 0<s)
    (input : List (GeneralPaperOrderedProfitTreeBuild.WeightedField Tag K))
    (hInput : ∀ field∈input,Leaves s (.leaf field.1)) :
    Leaves s (GeneralPaperOrderedProfitTreeBuild.build height (GeneralPaperOrderedProfitTreeBuild.pad height input)) := by
  apply build_leaves s height hs
  intro field hf
  rcases List.mem_append.mp hf with hf|hf
  · exact hInput field hf
  · have he := (List.mem_replicate.mp hf).2
    subst field
    exact dummy_leaves K s hs

theorem native_field {m k : ℕ} (T weight : ℕ) (ready : GeneralPaperCatalogueOptimizer.Ready m k)
    (prefixes : GeneralPaperUnsignedCellConstancy.Prefix k) (j : Fin m) :
    Leaves (ready.alphabet.lambda+1) (.leaf (GeneralPaperOrderedNativeOptionProfits.build k T weight prefixes (ready.cached.read j)).1) := by
  intro i
  rw [GeneralPaperOrderedNativeOptionProfits.read_build]
  exact GeneralPaperTagHeight.ready_height ready j i

theorem native_input {m k : ℕ} (T : ℕ) (ready : GeneralPaperCatalogueOptimizer.Ready m k)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (GeneralPaperUnsignedCellConstancy.Prefix k))
    (field : GeneralPaperOrderedProfitTreeBuild.WeightedField Tag ((GeneralPaperSourceParameters.prepare k).summarySize+2))
    (hf : field∈GeneralPaperOrderedNativeProfitOptimizer.weightedFields k T weights prefixes ready.cached) :
    Leaves (ready.alphabet.lambda+1) (.leaf field.1) := by
  obtain ⟨j,hj⟩ := List.mem_ofFn.mp hf
  rw [←hj]
  exact native_field T (weights.read j) ready (prefixes.read j) j

theorem native_tree {m k : ℕ} (prepared : GeneralPaperProfitParameters.Prepared) (T : ℕ)
    (ready : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (GeneralPaperUnsignedCellConstancy.Prefix k)) :
    Leaves (ready.alphabet.lambda+1) (GeneralPaperOrderedNativeProfitOptimizer.inputTree prepared T weights prefixes ready.cached) :=
  padded_leaves _ _ (by omega) _ (native_input T ready weights prefixes)

theorem native_states {m k : ℕ} (prepared : GeneralPaperProfitParameters.Prepared) (T : ℕ)
    (ready : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (GeneralPaperUnsignedCellConstancy.Prefix k)) :
    GeneralPaperOrderedTableHeight.Safe (expressionHeightBudget (ready.alphabet.lambda+1) prepared.parameters.height)
      (run prepared.grid (GeneralPaperOrderedNativeProfitOptimizer.inputTree prepared T weights prefixes ready.cached)).table :=
  states prepared.grid _ _ (native_tree prepared T ready weights prefixes)

end Blotto.GeneralPaperOrderedDPHeight
