import Blotto.GeneralPaperSharedResidentStorage

/-! Native profit-input fields own integer numerators and exact resource
tags. The numerator cap follows the reached prefix and retained weights;
leaf tag heights follow the actual Ready catalogue. -/
namespace Blotto.GeneralPaperEncodedProfitField
open GeneralPaperResponseTag GeneralPaperOrderedProfitDP GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Prefix)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def optionBits (W : ℕ) (x : ℕ × Tag) : ℕ :=
  natBits x.1+rationalWordWidth x.2.threshold+1+24*W

def footprint {K : ℕ} (W : ℕ) (f : Field Tag K) : ℕ :=
  GeneralPaperEncodedFixedVector.footprint W (optionBits W) f

def profile (W K H s : ℕ) : ℕ := K*(H+(1+2*s)+1+25*W)+32*W

theorem bounded {K : ℕ} (W H s : ℕ) (f : Field Tag K)
    (hp : ∀ i,natBits (f.read i).1≤H)
    (ht : ∀ i,RationalHeight (f.read i).2.threshold s) :
    footprint W f≤profile W K H s := by
  have hf := GeneralPaperEncodedFixedVector.bounded W (H+(1+2*s)+1+24*W) (optionBits W) f (by
    intro i
    have hn := hp i
    have hr := rationalWordWidth_of_height (ht i)
    unfold optionBits
    omega)
  exact hf.trans_eq (by unfold profile; ring)

theorem numerator_word {K k : ℕ} (m lambda Qv weight : ℕ) (prefixes : Prefix k)
    (plan : GeneralPaperOrderedNativeOptionProfits.Plan Tag k K)
    (hWeight : weight≤Qv) (hMesh : plan.mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator)
    (hGood : GeneralPaperMeshPrefixInvariant.Good m lambda k Qv prefixes) (i : Fin K) :
    natBits ((GeneralPaperOrderedNativeOptionProfits.build k
      (GeneralPaperTrajectoryParameters.prepare lambda k).rows weight prefixes plan).1.read i).1≤
      GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv := by
  have hp := GeneralPaperMeshCountBounds.cached_interval_bound false (fun _ => 1) 1 m lambda Qv plan.mesh
    prefixes plan.tails.positive i.castSucc (Fin.last K) hMesh hGood
  rw [GeneralPaperCachedMeshIntervalQuery.cached_data false (fun _ => 1) 1 plan.mesh _ _ _ _ hMesh] at hp
  change (GeneralPaperSignedTailPlan.evaluate k prefixes plan.tails i).positive≤plan.mesh at hp
  have hn := GeneralPaperNativeProfitOperands.profit_bound
    (GeneralPaperTrajectoryParameters.prepare lambda k).rows Qv plan.mesh weight
    (GeneralPaperSignedTailPlan.evaluate k prefixes plan.tails i).positive
    (GeneralPaperSignedTailPlan.evaluate k prefixes plan.tails i).negative hWeight hp
  have hcap := GeneralPaperNativeProfitOperands.cap_large (GeneralPaperTrajectoryParameters.prepare lambda k).rows Qv plan.mesh
  have hw := Nat.add_le_add_left (binaryWordWidth_mono (hn.trans hcap.1)) 1
  rw [hMesh] at hw
  rw [GeneralPaperOrderedNativeOptionProfits.read_build]
  rw [hMesh]
  exact hw.trans (GeneralPaperNativeProfitOperands.operand_word m lambda k Qv)

theorem ready {m k : ℕ} (W Qv : ℕ) (r : GeneralPaperCatalogueOptimizer.Ready m k)
    (weight : ℕ) (prefixes : Prefix k) (j : Fin m) (hWeight : weight≤Qv)
    (hGood : GeneralPaperMeshPrefixInvariant.Good m r.alphabet.lambda k Qv prefixes) :
    footprint W (GeneralPaperOrderedNativeOptionProfits.build k
      (GeneralPaperTrajectoryParameters.prepare r.alphabet.lambda k).rows weight prefixes (r.cached.read j)).1≤
      profile W ((GeneralPaperSourceParameters.prepare k).summarySize+2)
        (GeneralPaperPowerPreparationEnvelope.operandWidth m r.alphabet.lambda k Qv) (r.alphabet.lambda+1) := by
  apply bounded
  · exact numerator_word m r.alphabet.lambda Qv weight prefixes _ hWeight (GeneralPaperActualNativeProfitFields.meshes r j) hGood
  · intro i
    rw [GeneralPaperOrderedNativeOptionProfits.tag_preserved]
    exact GeneralPaperTagHeight.ready_height r j i

theorem dummy (W K H s : ℕ) (hH : 2≤H) (hs : 0<s) :
    footprint W (GeneralPaperOrderedProfitTreeBuild.dummy Tag K).1≤profile W K H s := by
  apply bounded
  · intro i
    simp only [GeneralPaperOrderedProfitTreeBuild.dummy,FixedArrayTable.read_ofFn]
    change 2≤H
    exact hH
  · intro i
    simp only [GeneralPaperOrderedProfitTreeBuild.dummy,FixedArrayTable.read_ofFn]
    exact GeneralPaperTagHeight.zero_height s hs

end Blotto.GeneralPaperEncodedProfitField
