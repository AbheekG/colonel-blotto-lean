import Blotto.GeneralPaperEncodedProfitInput

/-! Encoded balanced input trees include every leaf array and all node
references/headers. Dummy leaves are conservatively counted with payload,
even though the implementation shares one zero array. -/
namespace Blotto.GeneralPaperEncodedProfitTree
open scoped BigOperators
open GeneralPaperResponseTag GeneralPaperOrderedProfitDP
open GeneralPaperUnsignedCellConstancy (Prefix)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def footprint {K : ℕ} (W : ℕ) : {h : ℕ} → Tree Tag K h → ℕ
  | _,.leaf field => GeneralPaperEncodedProfitField.footprint W field+16*W
  | _,.node left right => footprint W left+footprint W right+32*W

def FieldsBound {K : ℕ} (W F : ℕ) : {h : ℕ} → Tree Tag K h → Prop
  | _,.leaf field => GeneralPaperEncodedProfitField.footprint W field≤F
  | _,.node left right => FieldsBound W F left ∧ FieldsBound W F right

theorem bounded {K h : ℕ} (W F : ℕ) (tree : Tree Tag K h) (hf : FieldsBound W F tree) :
    footprint W tree≤2^h*(F+64*W) := by
  have strong : footprint W tree+32*W≤2^h*(F+64*W) := by
    induction tree with
    | leaf field => change GeneralPaperEncodedProfitField.footprint W field+16*W+32*W≤1*(F+64*W); change _≤F at hf; omega
    | @node h left right ihl ihr =>
      have hl := ihl hf.1
      have hr := ihr hf.2
      dsimp only [footprint]
      rw [pow_succ]
      nlinarith only [hl,hr]
  omega

theorem build_bound {K : ℕ} (W F height : ℕ)
    (input : List (GeneralPaperOrderedProfitTreeBuild.WeightedField Tag K))
    (hz : GeneralPaperEncodedProfitField.footprint W (GeneralPaperOrderedProfitTreeBuild.dummy Tag K).1≤F)
    (hi : ∀ f∈input,GeneralPaperEncodedProfitField.footprint W f.1≤F) :
    FieldsBound W F (GeneralPaperOrderedProfitTreeBuild.build height input) := by
  induction height generalizing input with
  | zero =>
    cases input with
    | nil => exact hz
    | cons f rest => exact hi f List.mem_cons_self
  | succ h ih => exact ⟨ih _ (fun f hf => hi f (List.mem_of_mem_take hf)),
      ih _ (fun f hf => hi f (List.mem_of_mem_drop hf))⟩

theorem padded_bound {K : ℕ} (W F height : ℕ)
    (input : List (GeneralPaperOrderedProfitTreeBuild.WeightedField Tag K))
    (hz : GeneralPaperEncodedProfitField.footprint W (GeneralPaperOrderedProfitTreeBuild.dummy Tag K).1≤F)
    (hi : ∀ f∈input,GeneralPaperEncodedProfitField.footprint W f.1≤F) :
    FieldsBound W F (GeneralPaperOrderedProfitTreeBuild.build height (GeneralPaperOrderedProfitTreeBuild.pad height input)) := by
  apply build_bound W F height _ hz
  intro f hf
  rcases List.mem_append.mp hf with hf|hf
  · exact hi f hf
  · have he := (List.mem_replicate.mp hf).2
    subst f
    exact hz

theorem ready {m k : ℕ} (W Qv : ℕ) (prepared : GeneralPaperProfitParameters.Prepared)
    (r : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (Prefix k)) (hWeights : ∑ j,weights.read j=Qv)
    (hGood : ∀ j,GeneralPaperMeshPrefixInvariant.Good m r.alphabet.lambda k Qv (prefixes.read j)) :
    footprint W (GeneralPaperOrderedNativeProfitOptimizer.inputTree prepared
      (GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows weights prefixes r.cached)≤
      2^prepared.parameters.height*(GeneralPaperEncodedProfitInput.fieldProfile W m r.alphabet.lambda k Qv+64*W) := by
  apply bounded
  apply padded_bound
  · apply GeneralPaperEncodedProfitField.dummy
    · have hM := (GeneralPaperSourcePreparationEnvelope.base m r.alphabet.lambda k Qv).2
      unfold GeneralPaperPowerPreparationEnvelope.operandWidth
      omega
    · omega
  · exact GeneralPaperEncodedProfitInput.native_field W Qv r weights prefixes hWeights hGood

theorem priced_ready {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W localW Qv : ℕ)
    (prepared : GeneralPaperProfitParameters.Prepared) (hSpan : prepared.parameters.leafCount=2^prepared.parameters.height)
    (r : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (Prefix k)) (hWeights : ∑ j,weights.read j=Qv)
    (hGood : ∀ j,GeneralPaperMeshPrefixInvariant.Good m r.alphabet.lambda k Qv (prefixes.read j)) :
    footprint W (GeneralPaperNativeSelectorExecution.prepareTree bits index price localW prepared
      (GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows r weights prefixes).1≤
      2^prepared.parameters.height*(GeneralPaperEncodedProfitInput.fieldProfile W m r.alphabet.lambda k Qv+64*W) := by
  rw [GeneralPaperNativeSelectorExecution.prepareTree_data bits index price localW prepared _ r weights prefixes hSpan]
  exact ready W Qv prepared r weights prefixes hWeights hGood

theorem source_leaf_count (m lambda k Qv : ℕ) :
    2^(GeneralPaperProfitParameters.parameters m lambda k Qv).height≤2*m+1 := by
  rw [←GeneralPaperProfitParameters.leaf_count_spec]
  by_cases hm : 0<m
  · have h := GeneralPaperProfitParameters.leaf_count_upper m lambda k Qv hm
    omega
  · have hm0 : m=0 := by omega
    subst m
    change (GeneralPaperPowerCeiling.ceiling 0).power≤1
    rw [GeneralPaperPowerCeiling.ceiling,GeneralPaperPowerCeiling.loop]
    decide

theorem source {m k : ℕ} (W Qv : ℕ) (r : GeneralPaperCatalogueOptimizer.Ready m k)
    (weights : FixedArrayTable m ℕ) (prefixes : FixedArrayTable m (Prefix k))
    (hWeights : ∑ j,weights.read j=Qv)
    (hGood : ∀ j,GeneralPaperMeshPrefixInvariant.Good m r.alphabet.lambda k Qv (prefixes.read j)) :
    footprint W (GeneralPaperOrderedNativeProfitOptimizer.inputTree
      (GeneralPaperProfitParameters.prepare m r.alphabet.lambda k Qv)
      (GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows weights prefixes r.cached)≤
      (2*m+1)*(GeneralPaperEncodedProfitInput.fieldProfile W m r.alphabet.lambda k Qv+64*W) :=
  (ready W Qv _ r weights prefixes hWeights hGood).trans
    (Nat.mul_le_mul_right _ (source_leaf_count m r.alphabet.lambda k Qv))

end Blotto.GeneralPaperEncodedProfitTree
