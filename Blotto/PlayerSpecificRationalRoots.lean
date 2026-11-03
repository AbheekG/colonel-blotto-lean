import Blotto.PlayerSpecificReconstructionPrecision

/-! Complete executable rational-root enumeration for original degree-at-
most-three inputs. It computes its denominator/depth, isolates every real
root, and applies actual CF reconstruction plus exact substitution. There
is no sign restriction, denominator enumeration or integer-factor oracle.
Polynomial source-price refinement is a separate remaining obligation. -/
namespace Blotto.PlayerSpecificRationalRoots
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState
set_option autoImplicit false
set_option maxHeartbeats 5000000

def intervals (p : Data) : List Interval :=
  PlayerSpecificIsolationForest.run (prepare p) (PlayerSpecificReconstructionPrecision.depth p)
    (PlayerSpecificRootMagnitude.initial p (prepare p))

def reconstruct (p : Data) (node : Interval) : Option ℚ :=
  PlayerSpecificRationalReconstruction.run p (PlayerSpecificRootMagnitude.rootBound p)
    (PlayerSpecificReconstructionPrecision.depth p) (PlayerSpecificReconstructionPrecision.denominator p) node

def run (p : Data) : Data := (intervals p).filterMap (reconstruct p)

theorem sound (p : Data) (q : ℚ) (hq : q∈run p) : evaluate p q=0 := by
  obtain ⟨node,_,hsome⟩:=List.mem_filterMap.mp hq
  exact (PlayerSpecificRationalReconstruction.sound p _ _ _ node q hsome).2.2

theorem interval_cell (p : Data) (node : Interval) (hnode : node∈intervals p) :
    ∃ t,PlayerSpecificRootCells.Cell (PlayerSpecificRootMagnitude.rootBound p) (PlayerSpecificReconstructionPrecision.depth p) t node := by
  have h:=PlayerSpecificRootCells.forest_cells (prepare p) (PlayerSpecificRootMagnitude.rootBound p)
    (PlayerSpecificReconstructionPrecision.depth p) (PlayerSpecificRootMagnitude.initial p (prepare p)) 0 0
    (PlayerSpecificRootCells.initial_cell (prepare p) (PlayerSpecificRootMagnitude.rootBound p)) node hnode
  simpa only [Nat.zero_add] using h

theorem reconstruct_complete (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) (node : Interval)
    (hnode : node∈intervals p) (q : ℚ) (hq : node.lo<q ∧ q≤node.hi ∧ evaluate p q=0) : reconstruct p node=some q := by
  obtain ⟨t,ht⟩:=interval_cell p node hnode
  exact PlayerSpecificRationalReconstruction.complete p _ _ _ t node
    (PlayerSpecificRootMagnitude.rootBound_pos p) (PlayerSpecificReconstructionPrecision.denominator_pos p)
    ht (PlayerSpecificReconstructionPrecision.scale_sufficient p) q
    (PlayerSpecificReconstructionPrecision.normalized_denominator p hp hlen q hq.2.2) hq

theorem complete (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) (q : ℚ) (hq : evaluate p q=0) : q∈run p := by
  have hroot : PlayerSpecificSturmVariations.realEvaluate p (q:ℝ)=0 := by
    rw [PlayerSpecificSturmVariations.evaluate_cast,hq,Rat.cast_zero]
  obtain ⟨node,hnode,hcontains⟩:=
    (PlayerSpecificIsolationForest.coverage (prepare p) hp (PlayerSpecificReconstructionPrecision.depth p)
      (PlayerSpecificRootMagnitude.initial p (prepare p)) (PlayerSpecificRootMagnitude.initial_valid p (prepare p)) (q:ℝ) hroot).mp
        (PlayerSpecificRootMagnitude.initial_covers p hp (prepare p) (q:ℝ) hroot)
  have hlo : node.lo<q := by exact_mod_cast hcontains.1
  have hhi : q≤node.hi := by exact_mod_cast hcontains.2
  exact List.mem_filterMap.mpr ⟨node,hnode,reconstruct_complete p hp hlen node hnode q ⟨hlo,hhi,hq⟩⟩

theorem mem_iff (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) (q : ℚ) : q∈run p ↔ evaluate p q=0 :=
  ⟨sound p q,complete p hp hlen q⟩

theorem length_bound (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) : (run p).length≤3 := by
  have hlenf:=PlayerSpecificIsolationForest.length_bound (prepare p) hp (PlayerSpecificReconstructionPrecision.depth p)
    (PlayerSpecificRootMagnitude.initial p (prepare p)) (PlayerSpecificRootMagnitude.initial_valid p (prepare p))
  have hc:=PlayerSpecificIsolationBounds.count_bound (prepare p) hp
    (PlayerSpecificRootMagnitude.initial p (prepare p)) (PlayerSpecificRootMagnitude.initial_valid p (prepare p))
  have hf : (intervals p).length≤3 := by change (intervals p).length≤_ at hlenf; omega
  exact (List.length_filterMap_le _ _).trans hf

end Blotto.PlayerSpecificRationalRoots
