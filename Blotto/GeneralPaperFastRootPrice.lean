import Blotto.GeneralPaperSourceBudgetWidths

/-! Fast prices for complete root scan and native backtracking after the
balanced DP. Constructed source budgets fit a leaf word; root comparisons
therefore use the derived exact resource word, without an original-input
budget height. Only scalar bounds are enlarged; native tree types remain. -/
namespace Blotto.GeneralPaperFastRootPrice
open GeneralPaperFastRationalModel GeneralPaperFastOrderedDPPrice
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

def rootWord (m s : ℕ) : ℕ := (2*m+1)*(2*s+2)

theorem root_word_bound (m lambda k Qv s : ℕ) :
    GeneralPaperTagHeight.word s (GeneralPaperProfitParameters.parameters m lambda k Qv).height≤rootWord m s := by
  have hw := GeneralPaperBalancedTagWords.word_affine s (GeneralPaperProfitParameters.parameters m lambda k Qv).height
  have hn := Nat.mul_le_mul_right (2*s+2) (leaves_bound m lambda k Qv)
  dsimp only [rootWord]
  omega

theorem leaf_le_root (s h : ℕ) : GeneralPaperTagHeight.word s 0≤GeneralPaperTagHeight.word s h :=
  GeneralPaperTagHeight.word_mono s 0 h (Nat.zero_le _)

def selectionProfile (C d W m J s : ℕ) : ℕ :=
  GeneralPaperDPTableControls.labelsProfile W J+
    J*(2*charge C d (rootWord m s)+256*W+65*arrayWord W (J+2))+192*W

theorem selection_bound {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W m lambda k Qv J s budgetWord : ℕ) (hb : budgetWord≤GeneralPaperTagHeight.word s 0) :
    GeneralPaperRootSelectPrice.profile model.rat W J
      (expressionHeightBudget s (GeneralPaperProfitParameters.parameters m lambda k Qv).height) budgetWord≤
      selectionProfile C d W m J s := by
  have hw := root_word_bound m lambda k Qv s
  have hb' := hb.trans (leaf_le_root s (GeneralPaperProfitParameters.parameters m lambda k Qv).height)
  have hm : max (1+2*expressionHeightBudget s (GeneralPaperProfitParameters.parameters m lambda k Qv).height) budgetWord≤rootWord m s :=
    max_le hw (hb'.trans hw)
  have hp := (hg _).trans (charge_monotone C d hm)
  have hmul := Nat.mul_le_mul_left (2*J) hp
  dsimp only [GeneralPaperRootSelectPrice.profile,selectionProfile]
  nlinarith only [hmul]

def profile (C d W m lambda k Qv K J s : ℕ) : ℕ :=
  GeneralPaperFastOrderedDPPrice.fieldProfile C d W m lambda k Qv K J s+selectionProfile C d W m J s+
    256*(2*m+1)*(binaryWordWidth m+1)*arrayWord W (max K J+2)+128*W

theorem profile_bound {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W m lambda k Qv K J s budgetWord : ℕ) (hb : budgetWord≤GeneralPaperTagHeight.word s 0) :
    GeneralPaperOrderedRootPrice.profile model W m lambda k Qv K J s
      (GeneralPaperProfitParameters.parameters m lambda k Qv).height budgetWord≤profile C d W m lambda k Qv K J s := by
  have hd := (aggregate_bound hg W m lambda k Qv K J s _).trans (field_bound C d W m lambda k Qv K J s)
  have hs := selection_bound hg W m lambda k Qv J s budgetWord hb
  have hback := Nat.mul_le_mul_right (arrayWord W (max K J+2))
    (Nat.mul_le_mul (Nat.mul_le_mul_left 256 (leaves_bound m lambda k Qv)) (Nat.add_le_add_right (height_bound m lambda k Qv) 1))
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hd hs) hback) _

theorem native_work {m k : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : Growth model C d)
    (W Qv T : ℕ) (prepared : GeneralPaperProfitParameters.Prepared)
    (ready : GeneralPaperCatalogueOptimizer.Ready m k) (weights : FixedArrayTable m ℕ)
    (prefixes : FixedArrayTable m (GeneralPaperUnsignedCellConstancy.Prefix k)) (B : ℚ)
    (hp : prepared=GeneralPaperProfitParameters.prepare m ready.alphabet.lambda k Qv)
    (hT : T=(GeneralPaperTrajectoryParameters.prepare ready.alphabet.lambda k).rows) (hw : ∑ j,weights.read j=Qv)
    (hgood : ∀ j,GeneralPaperMeshPrefixInvariant.Good m ready.alphabet.lambda k Qv (prefixes.read j))
    (hb : rationalWordWidth B≤GeneralPaperTagHeight.word (ready.alphabet.lambda+1) 0) :
    let tree := GeneralPaperOrderedNativeProfitOptimizer.inputTree prepared T weights prefixes ready.cached
    (GeneralPaperOrderedRootExecution.run true (fun x => x) model.rat W prepared.grid tree (GeneralPaperResponseTag.budget B)).2+64*W≤
      profile C d W m ready.alphabet.lambda k Qv ((GeneralPaperSourceParameters.prepare k).summarySize+2)
        prepared.grid.size (ready.alphabet.lambda+1)+64*W := by
  have hn := (GeneralPaperOrderedRootPrice.native_work model W Qv T prepared ready weights prefixes B hp hT hw hgood).1
  have hh : prepared.parameters.height=(GeneralPaperProfitParameters.parameters m ready.alphabet.lambda k Qv).height := by rw [hp]; rfl
  have hc : GeneralPaperOrderedRootPrice.profile model W m ready.alphabet.lambda k Qv
      ((GeneralPaperSourceParameters.prepare k).summarySize+2) prepared.grid.size (ready.alphabet.lambda+1)
      prepared.parameters.height (rationalWordWidth B)≤
      profile C d W m ready.alphabet.lambda k Qv ((GeneralPaperSourceParameters.prepare k).summarySize+2)
        prepared.grid.size (ready.alphabet.lambda+1) := by
    rw [hh]
    exact profile_bound hg W m ready.alphabet.lambda k Qv _ _ _ _ hb
  exact hn.trans (Nat.add_le_add_right hc _)

end Blotto.GeneralPaperFastRootPrice
