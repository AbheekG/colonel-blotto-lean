import Blotto.GeneralPaperCompilerReference

/-! The common source/basis/index reference word is logarithmic in the
paper parameters. Large determinant values enter through encoded lengths;
they are not treated as polynomial-size natural values. -/
namespace Blotto.GeneralPaperCompilerReferenceGrowth
open GeneralPaperSourceWordGrowth GeneralPaperConstructedWordGrowth
open GeneralPaperNativeSourceWordGrowth GeneralPaperCompilerReference
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

@[fun_prop]
theorem labels_small : Small (fun x => (GeneralPaperProxyParameters.prepare x.m x.k).K) := by
  have he : (fun x : Input => (GeneralPaperProxyParameters.prepare x.m x.k).K)=(fun x : Input => 2^(7+x.k)) :=
    funext (fun x => (GeneralPaperProxyParameters.data x.m x.k).1.trans (GeneralPaperScoreScaleParameters.label_power x.m x.k))
  rw [he]
  fun_prop

@[fun_prop]
theorem score_small : Small (fun x => (GeneralPaperProxyParameters.prepare x.m x.k).S) := by
  change Small (fun x => (GeneralPaperPowerCeiling.ceiling (x.m*(GeneralPaperScoreScaleParameters.powerRun (7+x.k)).power)).power)
  fun_prop

@[fun_prop]
theorem dimension_small : Small (fun x => (GeneralPaperProxyParameters.prepare x.m x.k).d) := by
  have he : (fun x : Input => (GeneralPaperProxyParameters.prepare x.m x.k).d)=
      (fun x => x.m*((GeneralPaperProxyParameters.prepare x.m x.k).K-1)) :=
    funext (fun x => (GeneralPaperProxyParameters.data x.m x.k).2.2.1)
  rw [he]
  fun_prop

@[fun_prop]
theorem determinant_length_small : Small (fun x => binaryWordWidth (GeneralPaperProxyParameters.prepare x.m x.k).H) := by
  apply dominated (g:=fun x => 1+((GeneralPaperProxyParameters.prepare x.m x.k).d+2)*binaryWordWidth (x.m+3))
  · fun_prop
  · intro x
    exact GeneralPaperProxyWidths.H_width x.m x.k

@[fun_prop]
theorem basis_profile_small : Small (fun x => GeneralPaperEncodedBasisStorage.paperProfile 1 x.m x.k) := by
  unfold GeneralPaperEncodedBasisStorage.paperProfile GeneralPaperEncodedBasisStorage.profile
    GeneralPaperEncodedBasisStorage.rowProfile GeneralPaperEncodedBasisStorage.arrayProfile
    GeneralPaperEncodedBasisStorage.rowWork GeneralPaperEncodedScalarStorage.natBits
  dsimp only
  fun_prop

@[fun_prop]
theorem indices_small : Small (fun x => indexSize x.m x.k) := by
  unfold indexSize
  change Small (fun x => x.m*((GeneralPaperProxyParameters.prepare x.m x.k).K-1)+3+
    ((GeneralPaperProxyParameters.prepare x.m x.k).K+1)+(x.m+1)+((GeneralPaperProxyParameters.prepare x.m x.k).S+2)+
    (((GeneralPaperProxyParameters.prepare x.m x.k).S+1)*((GeneralPaperProxyParameters.prepare x.m x.k).K*(GeneralPaperProxyParameters.prepare x.m x.k).K)+3)+
    ((GeneralPaperProxyParameters.prepare x.m x.k).S+4)+(x.m+(GeneralPaperProxyParameters.prepare x.m x.k).K+1)+
    (2*(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows+(GeneralPaperProxyParameters.prepare x.m x.k).K+x.m+1))
  fun_prop

theorem at_one_small (C d : ℕ) : Small (fun x => profile C d 1 x) := by
  have hs := GeneralPaperSourceRowsReference.at_one_small C d
  unfold profile
  fun_prop

theorem width_tight (C d : ℕ) : Tight (width C d) :=
  tight_add _ _ (tight_mul_left 4 _ (word_tight _ (at_one_small C d)))
    GeneralPaperLogarithmicSourceReference.controls_tight

theorem logarithmic_width (C d : ℕ) : ∃ A : ℕ,∀ x,width C d x≤A*logSize x := width_tight C d

theorem source_paper_space {actual : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth actual C d) :
    ∃ A e : ℕ,∀ (x : Input) (first : Bool),1≤x.m →
      GeneralPaperSourceRowsStorageContract.live actual (width C d x) x first≤
        A*GeneralPaperSharpSourceSpaceRate.paperRate x*(logSize x)^e := by
  rcases GeneralPaperSourceRowsReference.profile_soft C d (width C d) (width_tight C d) with ⟨A,e,hA⟩
  refine ⟨8*A,e,?_⟩
  intro x first hm
  exact (GeneralPaperSourceRowsStorageContract.live_profile hg _ x first).trans ((hA x).trans
    ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left A (GeneralPaperSharpSourceSpaceRate.nonempty_rate x hm))).trans_eq (by ring)))

end Blotto.GeneralPaperCompilerReferenceGrowth
