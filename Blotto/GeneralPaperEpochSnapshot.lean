import Blotto.GeneralPaperEpochFieldState

/-! Four numerical blocks are all materialized from the same pre-update
state. Power preparation is shared and passed into the round. Positivity is
derived from the exact local-level cap and stored power certificates.
-/
namespace Blotto.GeneralPaperEpochSnapshot
open scoped BigOperators
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
open GeneralPaperEpochFieldState
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Block (k : ℕ) where
  values : Summary k
  cdf : Prefix k

def block {k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (levels : Summary k) : Block k :=
  let values := GeneralPaperEpochPowerQueries.buildNumerators prepared levels
  ⟨values,GeneralPaperEpochPrefixArray.build values⟩

structure Snapshot (k : ℕ) where
  p : Block k
  q : Block k
  lambda : Block k
  mu : Block k

def take {k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (state : State k) : Snapshot k :=
  ⟨block prepared state.pOccurrences,block prepared state.qOccurrences,
    block prepared state.lambdaOccurrences,block prepared state.muOccurrences⟩

def Block.Positive {k : ℕ} (b : Block k) : Prop := 0<∑ r, b.values.read r

def Positive {k : ℕ} (snapshot : Snapshot k) : Prop :=
  snapshot.p.Positive ∧ snapshot.q.Positive ∧ snapshot.lambda.Positive ∧ snapshot.mu.Positive

def Block.Coherent {k : ℕ} (b : Block k) : Prop := b.cdf=GeneralPaperEpochPrefixArray.build b.values

def Coherent {k : ℕ} (snapshot : Snapshot k) : Prop :=
  snapshot.p.Coherent ∧ snapshot.q.Coherent ∧ snapshot.lambda.Coherent ∧ snapshot.mu.Coherent

theorem take_coherent {k : ℕ} (prepared : GeneralPaperPreparedPowers.Prepared) (state : State k) : Coherent (take prepared state) :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem numerator_positive (lambda k degree : ℕ) (hDegree : degree≤GeneralPaperPowerPrecision.levelBound lambda k) :
    0<GeneralPaperLocalPowerNumerators.numerator (GeneralPaperPreparedPowers.prepare lambda k).format.unit
      (GeneralPaperPreparedPowers.prepare lambda k).format.fractionalBits
      (GeneralPaperPreparedPowers.query (GeneralPaperPreparedPowers.prepare lambda k) degree).number := by
  have hp := (GeneralPaperPreparedPowers.query_certificate lambda k degree hDegree).2.2.1
  unfold GeneralPaperLocalPowerNumerators.numerator
  split_ifs <;> omega

theorem block_positive (lambda k : ℕ) (levels : Summary k)
    (hLevels : ∀ r, levels.read r≤GeneralPaperPowerPrecision.levelBound lambda k) :
    (block (GeneralPaperPreparedPowers.prepare lambda k) levels).Positive := by
  have hs : 0<(GeneralPaperSourceParameters.prepare k).summarySize := by
    rw [(GeneralPaperSourceParameters.data k).2.2.2.2.2]
    positivity
  let r : Fin (GeneralPaperSourceParameters.prepare k).summarySize := ⟨0,hs⟩
  have he := numerator_positive lambda k (levels.read r) (hLevels r)
  have hRead : 0<(block (GeneralPaperPreparedPowers.prepare lambda k) levels).values.read r := by
    change 0<(GeneralPaperEpochPowerQueries.buildNumerators _ levels).read r
    rw [GeneralPaperEpochPowerQueries.read_numerators]
    exact he
  exact lt_of_lt_of_le hRead (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ r))

theorem take_positive (lambda k : ℕ) (state : State k) (hState : Bounded state (GeneralPaperPowerPrecision.levelBound lambda k)) :
    Positive (take (GeneralPaperPreparedPowers.prepare lambda k) state) :=
  ⟨block_positive lambda k state.pOccurrences hState.1,
    block_positive lambda k state.qOccurrences hState.2.1,
    block_positive lambda k state.lambdaOccurrences hState.2.2.1,
    block_positive lambda k state.muOccurrences hState.2.2.2.1⟩

end Blotto.GeneralPaperEpochSnapshot
