import Blotto.BinaryScalarTape
import Blotto.BinaryWordSegmentEmissionLifetime

/-! Original normalized segment fields and cached coefficients derive the
complete draw-to-emission reservation in both uniform and mixed-pivot paths.
No reached-row width/height or emission-price oracle is assumed. -/
namespace Blotto.BinaryWordSegmentEmissionBound
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryStoredSegmentProgram BinaryWordSegmentResultHeight
open BinaryWordSegmentEmissionLifetime
set_option maxHeartbeats 2000000

def uniformEnvelope (n m k s K indexWidth seedCap : ℕ) : ℕ :=
  BinaryWordSegmentLifetimeBound.envelope m k s K indexWidth seedCap +
    BinaryGroupEmissionLifetimeBound.envelope n (2 * rowHeight s K + 1) + 64

def mixedEnvelope (n m k s K indexWidth seedCap : ℕ) : ℕ :=
  BinaryWordSegmentLifetimeBound.envelope (m + 1) k s K indexWidth seedCap +
    BinaryGroupEmissionLifetimeBound.mixedEnvelope n m (rowHeight s K) + 64

theorem uniformRun_usage {n m k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared m k) (fallback : Fin k)
    (source : RationalSegmentLottery m k) (hR : prepared.table.Refines source)
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (hRoutesC : ∀ j,CanonicalWord (routes.read j).2)
    (s : ℕ) (hs : 3 ≤ s) (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) s)
    (hWeight : ∀ slot,RationalHeight (source.weight slot) s)
    (hEndpoints : ∀ slot j,RationalHeight (source.P slot j) s ∧ RationalHeight (source.Q slot j) s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (uniformRun store prepared fallback routes K scalar pc hp).2 ≤ uniformEnvelope n m k s K store.width store.cap.value := by
  let drawn := BinaryWordSegmentLifetime.runWithTrace store prepared fallback K scalar pc hp
  have hTable : ∀ slot j,RationalHeight (value ((prepared.table.P.read slot).read j)) s ∧
      RationalHeight (value ((prepared.table.Q.read slot).read j)) s := by
    intro slot j
    rw [hR.2.1 slot j,hR.2.2 slot j]
    exact hEndpoints slot j
  have hDraw := BinaryWordSegmentLifetimeBound.runWithTrace_usage store prepared source hR s hs hWeight hEndpoints fallback K scalar pc hp
  have hRW : ∀ j,width (routes.read j).2 ≤ 2 * rowHeight s K + 1 := by
    intro j
    have h := (hRoutesC j).2.trans (rationalWordWidth_of_height ((hRoutes j).mono (rowHeight_ge s K)))
    omega
  have hRowW : ∀ row,drawn.1.1 = some row → ∀ g,width (row.read g) ≤ 2 * rowHeight s K + 1 := by
    intro row hRow g
    have hc := success_canonical store prepared fallback K scalar pc hp row hRow g
    have hh := success_height store prepared fallback s (by omega) hTable K scalar pc hp row hRow g
    have h := hc.2.trans (rationalWordWidth_of_height hh)
    omega
  have hEmit := BinaryGroupEmissionLifetimeBound.emitOptionWithTrace_usage routes drawn.1.1 _ hRW hRowW
  have hw := wrap_usage 32 2 [drawn.2,(BinaryGroupEmissionLifetime.emitOptionWithTrace routes drawn.1.1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [drawn.2,(BinaryGroupEmissionLifetime.emitOptionWithTrace routes drawn.1.1).2]) ≤ _
  change usage drawn.2 ≤ _ at hDraw
  unfold uniformEnvelope
  omega

theorem mixedRun_usage {n m k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared (m + 1) k) (fallback : Fin k)
    (source : RationalSegmentLottery (m + 1) k) (hR : prepared.table.Refines source)
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n) (hRoutesC : ∀ j,CanonicalWord (routes.read j).2)
    (s : ℕ) (hs : 3 ≤ s) (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) s)
    (hWeight : ∀ slot,RationalHeight (source.weight slot) s)
    (hEndpoints : ∀ slot j,RationalHeight (source.P slot j) s ∧ RationalHeight (source.Q slot j) s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    usage (mixedRun store prepared fallback routes pivot K scalar pc hp).2 ≤ mixedEnvelope n m k s K store.width store.cap.value := by
  let drawn := BinaryWordSegmentLifetime.runWithTrace store prepared fallback K scalar pc hp
  have hTable : ∀ slot j,RationalHeight (value ((prepared.table.P.read slot).read j)) s ∧
      RationalHeight (value ((prepared.table.Q.read slot).read j)) s := by
    intro slot j
    rw [hR.2.1 slot j,hR.2.2 slot j]
    exact hEndpoints slot j
  have hDraw := BinaryWordSegmentLifetimeBound.runWithTrace_usage store prepared source hR s hs hWeight hEndpoints fallback K scalar pc hp
  have hRowC := success_canonical store prepared fallback K scalar pc hp
  have hRowH := success_height store prepared fallback s (by omega) hTable K scalar pc hp
  have hEmit := BinaryGroupEmissionLifetimeBound.emitMixedOptionWithTrace_usage routes pivot drawn.1.1 hRoutesC hRowC
    (rowHeight s K) (hs.trans (rowHeight_ge s K)) (fun j => (hRoutes j).mono (rowHeight_ge s K)) hRowH
  have hw := wrap_usage 32 2 [drawn.2,(BinaryGroupEmissionLifetime.emitMixedOptionWithTrace routes pivot drawn.1.1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 32 2 [drawn.2,(BinaryGroupEmissionLifetime.emitMixedOptionWithTrace routes pivot drawn.1.1).2]) ≤ _
  change usage drawn.2 ≤ _ at hDraw
  unfold mixedEnvelope
  omega

theorem uniform_all_prefix {n m k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared m k) (fallback : Fin k)
    (source : RationalSegmentLottery m k) (hR : prepared.table.Refines source)
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (hRoutesC : ∀ j,CanonicalWord (routes.read j).2)
    (s : ℕ) (hs : 3 ≤ s) (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) s)
    (hWeight : ∀ slot,RationalHeight (source.weight slot) s)
    (hEndpoints : ∀ slot j,RationalHeight (source.P slot j) s ∧ RationalHeight (source.Q slot j) s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ) :
    retainedHeap borrowed (uniformRun store prepared fallback routes K scalar pc hp).2 steps ≤
        borrowed + uniformEnvelope n m k s K store.width store.cap.value ∧
      framePeak ((uniformRun store prepared fallback routes K scalar pc hp).2.take steps) ≤ uniformEnvelope n m k s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (uniformRun_usage store prepared fallback source hR routes hRoutesC s hs hRoutes hWeight hEndpoints K scalar pc hp) borrowed steps

theorem mixed_all_prefix {n m k : ℕ} (store : BinarySeedLookupTree.Store) (prepared : Prepared (m + 1) k) (fallback : Fin k)
    (source : RationalSegmentLottery (m + 1) k) (hR : prepared.table.Refines source)
    (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n) (hRoutesC : ∀ j,CanonicalWord (routes.read j).2)
    (s : ℕ) (hs : 3 ≤ s) (hRoutes : ∀ j,RationalHeight (value (routes.read j).2) s)
    (hWeight : ∀ slot,RationalHeight (source.weight slot) s)
    (hEndpoints : ∀ slot j,RationalHeight (source.P slot j) s ∧ RationalHeight (source.Q slot j) s)
    (K : ℕ) (scalar : BinaryScalarTape K) (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) (borrowed steps : ℕ) :
    retainedHeap borrowed (mixedRun store prepared fallback routes pivot K scalar pc hp).2 steps ≤
        borrowed + mixedEnvelope n m k s K store.width store.cap.value ∧
      framePeak ((mixedRun store prepared fallback routes pivot K scalar pc hp).2.take steps) ≤ mixedEnvelope n m k s K store.width store.cap.value :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (mixedRun_usage store prepared fallback source hR routes pivot hRoutesC s hs hRoutes hWeight hEndpoints K scalar pc hp) borrowed steps

end Blotto.BinaryWordSegmentEmissionBound
