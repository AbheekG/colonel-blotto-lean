import Blotto.GeneralPaperFastRationalBounds

/-! Interpret the checked balanced ordered DP in the paper's fast-rational
model. The exact all-level resource-word total remains linear in the padded
field count and leaf word, up to the tree height. Short grid operands stay
separate; no uniform full-alphabet operand is charged at every node. -/
namespace Blotto.GeneralPaperFastOrderedDPPrice
open GeneralPaperFastRationalModel GeneralPaperOrderedDPAggregatePrice
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

def resourceWords (s H : ℕ) : ℕ := (H+1)*2^H*(2*s+2)

def profile (C d W m lambda k Qv K J s H : ℕ) : ℕ :=
  2^H*(leafBase (charge C d) W m lambda k Qv K J+mergeBase (charge C d) W m lambda k Qv J)+
    (2*K+4*J^2)*charge C d (resourceWords s H)

theorem leaf_bound {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W m lambda k Qv K J : ℕ) :
    leafBase model.rat W m lambda k Qv K J≤leafBase (charge C d) W m lambda k Qv K J := by
  unfold leafBase GeneralPaperCachedProfitGridPrice.profile
  dsimp only
  gcongr
  exact hg _

theorem merge_bound {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W m lambda k Qv J : ℕ) :
    mergeBase model.rat W m lambda k Qv J≤mergeBase (charge C d) W m lambda k Qv J := by
  unfold mergeBase GeneralPaperCachedProfitGridPrice.profile
  dsimp only
  gcongr <;> exact hg _

theorem balanced_resource_bound {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (s H : ℕ) : GeneralPaperBalancedTagWords.profile model.rat s H≤charge C d (resourceWords s H) :=
  (GeneralPaperBalancedTagPrice.aggregate model s H).trans (hg _)

theorem aggregate_bound {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W m lambda k Qv K J s H : ℕ) :
    GeneralPaperOrderedDPAggregatePrice.profile model W m lambda k Qv K J s H≤profile C d W m lambda k Qv K J s H := by
  dsimp only [GeneralPaperOrderedDPAggregatePrice.profile,profile,resourceWords]
  exact Nat.add_le_add
    (Nat.mul_le_mul_left _ (Nat.add_le_add (leaf_bound hg W m lambda k Qv K J) (merge_bound hg W m lambda k Qv J)))
    (Nat.mul_le_mul_left _ (hg _))

theorem bit_profile_bound {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W m lambda k Qv K J s H : ℕ) :
    GeneralPaperOrderedDPPrice.bitProfile model.rat W m lambda k Qv K J s H≤profile C d W m lambda k Qv K J s H :=
  (GeneralPaperOrderedDPAggregatePrice.bound model W m lambda k Qv K J s H).trans
    (aggregate_bound hg W m lambda k Qv K J s H)

theorem native_tree {K h : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W m lambda k Qv s : ℕ) (prepared : GeneralPaperProfitParameters.Prepared)
    (hp : prepared=GeneralPaperProfitParameters.prepare m lambda k Qv)
    (tree : GeneralPaperOrderedProfitDP.Tree GeneralPaperResponseTag.Tag K h)
    (hl : GeneralPaperOrderedDPHeight.Leaves s tree)
    (hn : GeneralPaperOrderedDPProfitCaps.Leaves (2*prepared.parameters.qProf) tree) :
    (GeneralPaperOrderedDPExecution.run true (fun x => x) model.rat W prepared.grid tree).2≤
      profile C d W m lambda k Qv K prepared.grid.size s h :=
  (GeneralPaperOrderedDPAggregatePrice.work model W m lambda k Qv s prepared hp tree hl hn).trans
    (aggregate_bound hg W m lambda k Qv K prepared.grid.size s h)

theorem height_bound (m lambda k Qv : ℕ) :
    (GeneralPaperProfitParameters.parameters m lambda k Qv).height≤binaryWordWidth m :=
  GeneralPaperProfitParameters.height_minimal m lambda k Qv _ (lt_pow_binaryWordWidth m).le

theorem leaves_bound (m lambda k Qv : ℕ) :
    2^(GeneralPaperProfitParameters.parameters m lambda k Qv).height≤2*m+1 := by
  rw [←GeneralPaperProfitParameters.leaf_count_spec]
  by_cases hm : m=0
  · subst m
    change (GeneralPaperPowerCeiling.ceiling 0).power≤1
    rw [GeneralPaperPowerCeiling.ceiling_power]
    have h := GeneralPaperPowerCeiling.ceiling_minimal 0 0 (by decide)
    have he : (GeneralPaperPowerCeiling.ceiling 0).doublings=0 := by omega
    rw [he]
    decide
  · exact (GeneralPaperProfitParameters.leaf_count_upper m lambda k Qv (by omega)).le.trans (by omega)

def fieldResourceWords (m s : ℕ) : ℕ := (binaryWordWidth m+1)*(2*m+1)*(2*s+2)

theorem resource_bound (m lambda k Qv s : ℕ) :
    resourceWords s (GeneralPaperProfitParameters.parameters m lambda k Qv).height≤fieldResourceWords m s :=
  Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.add_le_add_right (height_bound m lambda k Qv) 1) (leaves_bound m lambda k Qv))

def fieldProfile (C d W m lambda k Qv K J s : ℕ) : ℕ :=
  (2*m+1)*(leafBase (charge C d) W m lambda k Qv K J+mergeBase (charge C d) W m lambda k Qv J)+
    (2*K+4*J^2)*charge C d (fieldResourceWords m s)

theorem field_bound (C d W m lambda k Qv K J s : ℕ) :
    profile C d W m lambda k Qv K J s (GeneralPaperProfitParameters.parameters m lambda k Qv).height≤
      fieldProfile C d W m lambda k Qv K J s :=
  Nat.add_le_add (Nat.mul_le_mul_right _ (leaves_bound m lambda k Qv))
    (Nat.mul_le_mul_left _ (charge_monotone C d (resource_bound m lambda k Qv s)))

theorem native_ready {m k : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W Qv T : ℕ) (prepared : GeneralPaperProfitParameters.Prepared)
    (ready : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (GeneralPaperUnsignedCellConstancy.Prefix k))
    (hp : prepared=GeneralPaperProfitParameters.prepare m ready.alphabet.lambda k Qv)
    (hT : T=(GeneralPaperTrajectoryParameters.prepare ready.alphabet.lambda k).rows)
    (hw : ∑ j,weights.read j=Qv)
    (hgood : ∀ j,GeneralPaperMeshPrefixInvariant.Good m ready.alphabet.lambda k Qv (prefixes.read j)) :
    let tree := GeneralPaperOrderedNativeProfitOptimizer.inputTree prepared T weights prefixes ready.cached
    (GeneralPaperOrderedDPExecution.run true (fun x => x) model.rat W prepared.grid tree).2≤
      fieldProfile C d W m ready.alphabet.lambda k Qv ((GeneralPaperSourceParameters.prepare k).summarySize+2)
        prepared.grid.size (ready.alphabet.lambda+1) := by
  have hn := (GeneralPaperOrderedDPPrice.native_work model W Qv T prepared ready weights prefixes hp hT hw hgood).1
  have hb := bit_profile_bound hg W m ready.alphabet.lambda k Qv ((GeneralPaperSourceParameters.prepare k).summarySize+2)
    prepared.grid.size (ready.alphabet.lambda+1) prepared.parameters.height
  have hh : prepared.parameters.height=(GeneralPaperProfitParameters.parameters m ready.alphabet.lambda k Qv).height := by rw [hp]; rfl
  have hc : GeneralPaperFastOrderedDPPrice.profile C d W m ready.alphabet.lambda k Qv
      ((GeneralPaperSourceParameters.prepare k).summarySize+2) prepared.grid.size (ready.alphabet.lambda+1) prepared.parameters.height≤
      fieldProfile C d W m ready.alphabet.lambda k Qv ((GeneralPaperSourceParameters.prepare k).summarySize+2)
        prepared.grid.size (ready.alphabet.lambda+1) := by
    rw [hh]
    exact field_bound C d W m ready.alphabet.lambda k Qv _ _ _
  exact hn.trans (hb.trans hc)

end Blotto.GeneralPaperFastOrderedDPPrice
