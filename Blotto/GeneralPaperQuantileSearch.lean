import Blotto.GeneralPaperQuantileBracket

/-! The root search computes one common fresh total, descends with a zero
prefix, and encodes the resulting path once. Its certificate concerns the
exact normalized full-code law represented by the unchanged cached tree.
-/
namespace Blotto.GeneralPaperQuantileSearch
open GeneralPaperDyadicFloat GeneralPaperPreparedPowers GeneralPaperMassApproximation
open GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery GeneralPaperTreePrefix
open GeneralPaperQuantileDescent GeneralPaperNormalizedMassError GeneralPaperQuantileComparison
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Output where
  location : ℕ
  work : ℕ
  visits : ℕ

def search (prepared : Prepared) (width j s height : ℕ) (node : Node height) : Output :=
  let total := fresh prepared 0 node
  let descent := run prepared width j s total.number height node 0 total.number zero
  ⟨code descent,total.work+descent.work+8*descent.path.length+16,descent.visits⟩

def cdf (k : ℕ) {height : ℕ} (node : Node height) (count : ℕ) : ℚ :=
  weightedPrefix k 0 node count/trueMass k 0 node

theorem cdf_zero (k : ℕ) {height : ℕ} (node : Node height) : cdf k node 0=0 := by
  rw [cdf,weighted_zero,zero_div]

theorem cdf_total (k : ℕ) {height : ℕ} (node : Node height) : cdf k node (2^height)=1 := by
  rw [cdf,weighted_total,div_self (ne_of_gt (true_positive _ _ _))]

theorem cdf_monotone (k : ℕ) {height : ℕ} (node : Node height) : Monotone (cdf k node) := by
  intro a b hab
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (prefix_monotone _ (GeneralPaperCachedMassJoin.base_positive k).le node a b hab) (by positivity))
    (true_positive _ _ _).le

theorem cdf_bounds (k : ℕ) {height : ℕ} (node : Node height) (count : ℕ) (hCount : count≤2^height) :
    0≤cdf k node count ∧ cdf k node count≤1 := by
  have he := weighted_bounds k 0 node count hCount
  exact ⟨div_nonneg he.1 (true_positive _ _ _).le,
    (div_le_one (true_positive _ _ _)).mpr he.2⟩

theorem location_bound (prepared : Prepared) (width j s height : ℕ) (node : Node height) :
    (search prepared width j s height node).location<2^height :=
  code_bound _ _ _ _ _ _ _ _ _ _

theorem search_visits (prepared : Prepared) (width j s height : ℕ) (node : Node height) :
    (search prepared width j s height node).visits=height+1 := visits _ _ _ _ _ _ _ _ _ _

theorem search_bracket (lambda k j height : ℕ) (node : Node height)
    (hJ : j≤(GeneralPaperSourceParameters.prepare k).summarySize) (hHeight : height≤lambda+1)
    (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node) :
    let output := search (prepare lambda k) (width lambda k) j (GeneralPaperSourceParameters.prepare k).summarySize height node
    cdf k node output.location≤(j:ℚ)/(GeneralPaperSourceParameters.prepare k).summarySize+delta k ∧
      (j:ℚ)/(GeneralPaperSourceParameters.prepare k).summarySize-delta k≤cdf k node (output.location+1) := by
  have hMass := fresh_bound lambda k 0 node hHeight hValid hPath
  have hsNat : 0<(GeneralPaperSourceParameters.prepare k).summarySize := by
    rw [(GeneralPaperSourceParameters.data k).2.2.2.2.2]
    positivity
  have hs : (0:ℚ)<(GeneralPaperSourceParameters.prepare k).summarySize := by exact_mod_cast hsNat
  have ht : 0≤(j:ℚ)/(GeneralPaperSourceParameters.prepare k).summarySize := by positivity
  have hUpper : (j:ℚ)/(GeneralPaperSourceParameters.prepare k).summarySize≤1 := by
    apply (div_le_one hs).mpr
    exact_mod_cast hJ
  have hBracket : GeneralPaperQuantileBracket.Bracket 0 (trueMass k 0 node) (trueMass k 0 node)
      ((j:ℚ)/(GeneralPaperSourceParameters.prepare k).summarySize) (delta k) := by
    constructor
    · simpa only [zero_div] using add_nonneg ht (delta_nonnegative k)
    · rw [zero_add,div_self (ne_of_gt (true_positive _ _ _))]
      linarith [delta_nonnegative k]
  have he := GeneralPaperQuantileBracket.run_bracket lambda k j hJ
    (fresh (prepare lambda k) 0 node).number (trueMass k 0 node) (true_positive _ _ _) hMass
    height node 0 0 0 (fresh (prepare lambda k) 0 node).number zero (by omega) hValid hPath hMass
    (zero_bound _ _) (by simp) hBracket
  simpa only [search,code,GeneralPaperQuantilePath.encode_index,cdf,zero_add] using he

end Blotto.GeneralPaperQuantileSearch
