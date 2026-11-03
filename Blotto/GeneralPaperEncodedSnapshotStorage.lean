import Blotto.GeneralPaperEncodedReferenceVector

/-! The common pre-update snapshot owns four numerator and prefix arrays.
Actual bounded levels derive every stored word; prefix views only borrow
these arrays and do not duplicate their coordinate payloads. -/
namespace Blotto.GeneralPaperEncodedSnapshotStorage
open GeneralPaperEpochSnapshot GeneralPaperCatalogueEpochRun
open GeneralPaperCatalogueOccurrenceHistory
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def blockFootprint {k : ℕ} (W : ℕ) (b : Block k) : ℕ :=
  GeneralPaperEncodedNatArray.footprint W b.values+GeneralPaperEncodedNatArray.footprint W b.cdf+32*W

def blockProfile (W m lambda k Qv : ℕ) : ℕ :=
  (2*(GeneralPaperSourceParameters.prepare k).summarySize+1)*(GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv+W)+96*W

theorem numerator_word (m lambda k Qv x : ℕ) (hx : x≤4*(GeneralPaperPowerPrecision.prepare lambda k).unit) :
    1+binaryWordWidth x≤GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  have hs : 1≤(GeneralPaperSourceParameters.prepare k).summarySize := by
    rw [(GeneralPaperSourceParameters.data k).2.2.2.2.2]
    exact Nat.two_pow_pos _
  have hb := Nat.mul_le_mul_right (4*(GeneralPaperPowerPrecision.prepare lambda k).unit) hs
  simp only [Nat.one_mul] at hb
  exact (Nat.add_le_add_left (binaryWordWidth_mono (hx.trans hb)) 1).trans (GeneralPaperEpochNumeratorEnvelope.total_word m lambda k Qv)

theorem block_bound {k : ℕ} (W m lambda Qv : ℕ) (b : Block k)
    (hv : ∀ i,b.values.read i≤4*(GeneralPaperPowerPrecision.prepare lambda k).unit)
    (hc : GeneralPaperMeshPrefixInvariant.Good m lambda k Qv b.cdf) : blockFootprint W b≤blockProfile W m lambda k Qv := by
  have hp := GeneralPaperEncodedNatArray.bounded W _ b.values (fun i => numerator_word m lambda k Qv _ (hv i))
  have hq := GeneralPaperEncodedNatArray.bounded W _ b.cdf (GeneralPaperMeshPrefixInvariant.prefix_word m lambda k Qv b.cdf hc)
  unfold blockFootprint blockProfile
  nlinarith only [hp,hq]

def fieldFootprint {k : ℕ} (W : ℕ) (s : Snapshot k) : ℕ :=
  blockFootprint W s.p+blockFootprint W s.q+blockFootprint W s.lambda+blockFootprint W s.mu+64*W

def fieldProfile (W m lambda k Qv : ℕ) : ℕ := 4*blockProfile W m lambda k Qv+64*W

theorem take_bound {k : ℕ} (W m lambda Qv : ℕ) (state : GeneralPaperEpochFieldState.State k)
    (hb : GeneralPaperEpochFieldState.Bounded state (GeneralPaperPowerPrecision.levelBound lambda k)) :
    fieldFootprint W (take (GeneralPaperPreparedPowers.prepare lambda k) state)≤fieldProfile W m lambda k Qv := by
  have h (learner : Learner) := block_bound W m lambda Qv (block learner (take (GeneralPaperPreparedPowers.prepare lambda k) state))
    (GeneralPaperActualMeshPrefixInvariant.take_values_bound lambda k state hb learner)
    (GeneralPaperActualMeshPrefixInvariant.take_good m lambda k Qv state hb learner)
  have hp := h .p
  have hq := h .q
  have hl := h .lambda
  have hu := h .mu
  dsimp only [GeneralPaperCatalogueOccurrenceHistory.block] at hp hq hl hu
  unfold fieldFootprint fieldProfile
  omega

def familyFootprint {m k : ℕ} (W : ℕ) (snapshots : FixedArrayTable m (Snapshot k)) : ℕ :=
  (∑ j,fieldFootprint W (snapshots.read j))+m*W+64*W

def profile (W m lambda k Qv : ℕ) : ℕ := m*fieldProfile W m lambda k Qv+m*W+64*W

theorem selected {m k : ℕ} (W Qv : ℕ) (cache : GeneralPaperCatalogueEpochCache.Cache m k)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) :
    familyFootprint W (beforeAt (GeneralPaperCatalogueEpochRun.selected cache Qv weights Bc Br) time)≤profile W m cache.alphabet.lambda k Qv := by
  have h (j : Fin m) : fieldFootprint W ((beforeAt (GeneralPaperCatalogueEpochRun.selected cache Qv weights Bc Br) time).read j)≤
      fieldProfile W m cache.alphabet.lambda k Qv := by
    change fieldFootprint W (snapshotAt _ time j)≤_
    rw [snapshot_take]
    exact take_bound W m cache.alphabet.lambda Qv _ (selected_cap cache Qv weights Bc Br time ht j)
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => h j)
  have hb := Nat.add_le_add_right (Nat.add_le_add_right hs (m*W)) (64*W)
  simpa only [familyFootprint,profile,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using hb

theorem priced {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W Qv : ℕ)
    (cache : GeneralPaperCatalogueEpochCache.Cache m k) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (time : ℕ)
    (ht : time≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) :
    familyFootprint W (GeneralPaperEpochSnapshotFamilyPrice.run bits index price W c
      (stateAt (GeneralPaperCatalogueEpochRun.selected cache Qv weights Bc Br) time).fields).1≤profile W m cache.alphabet.lambda k Qv := by
  rw [GeneralPaperActualEpochSnapshotPrice.selected_data bits index price W Qv cache c hc]
  exact selected W Qv cache weights Bc Br time ht

end Blotto.GeneralPaperEncodedSnapshotStorage
