import Blotto.GeneralPaperCompilerReferenceGrowth

/-! The retained original-basis representation has soft cubic field and
inverse-accuracy storage, below the paper's fourth accuracy power. This is
a representation bound for the actual invariant states; it does not count
all endpoint temporaries or prove the complete compiler lifetime bound. -/
namespace Blotto.GeneralPaperBasisStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperCompilerReferenceGrowth GeneralPaperEncodedBasisStorage
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

@[fun_prop]
theorem labels : Rated (fun x => (GeneralPaperProxyParameters.prepare x.m x.k).K) 0 0 1 := by
  have he : (fun x : Input => (GeneralPaperProxyParameters.prepare x.m x.k).K)=(fun x : Input => 2^(7+x.k)) :=
    funext (fun x => (GeneralPaperProxyParameters.data x.m x.k).1.trans (GeneralPaperScoreScaleParameters.label_power x.m x.k))
  rw [he]
  exact dyadic_accuracy 7

@[fun_prop]
theorem reduced_labels : Rated (fun x => (GeneralPaperProxyParameters.prepare x.m x.k).K-1) 0 0 1 :=
  GeneralPaperSourceRateAlgebra.sub _ _ 0 0 1 labels

@[fun_prop]
theorem dimension : Rated (fun x => (GeneralPaperProxyParameters.prepare x.m x.k).d) 1 0 1 := by
  change Rated (fun x => x.m*((GeneralPaperProxyParameters.prepare x.m x.k).K-1)) 1 0 1
  exact GeneralPaperSourceRateAlgebra.mul _ _ 1 0 0 0 0 1 GeneralPaperSourceRateAlgebra.m reduced_labels

@[fun_prop]
theorem determinant_length : Rated (fun x => binaryWordWidth (GeneralPaperProxyParameters.prepare x.m x.k).H) 1 0 1 := by
  apply GeneralPaperSourceSoftBounds.dominated (g:=fun x => 1+((GeneralPaperProxyParameters.prepare x.m x.k).d+2)*binaryWordWidth (x.m+3))
  · change Rated (fun x => 1+((GeneralPaperProxyParameters.prepare x.m x.k).d+2)*binaryWordWidth (x.m+3)) 1 0 1
    source_space
  · intro x
    exact GeneralPaperProxyWidths.H_width x.m x.k

def certificate (W : Input → ℕ) (hW : Tight W) : Certificate (fun x => paperProfile (W x) x.m x.k) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  refine ⟨_,_,_,by
    unfold paperProfile profile rowProfile arrayProfile rowWork GeneralPaperEncodedScalarStorage.natBits
    dsimp only
    source_space⟩

theorem degrees (W : Input → ℕ) (hW : Tight W) :
    ((certificate W hW).fields,(certificate W hW).symbols,(certificate W hW).accuracy)=(3,0,3) := rfl

theorem profile_rate (W : Input → ℕ) (hW : Tight W) :
    Rated (fun x => paperProfile (W x) x.m x.k) 3 0 3 := (certificate W hW).bound

theorem common_word_bound (C d : ℕ) : ∃ A e : ℕ,∀ x,
    paperProfile (GeneralPaperCompilerReference.width C d x) x.m x.k≤
      A*(x.m+1)^3*2^(3*x.k)*(logSize x)^e := by
  rcases profile_rate (GeneralPaperCompilerReference.width C d) (width_tight C d) with ⟨A,e,hA⟩
  refine ⟨A,e,?_⟩
  intro x
  have he : (GeneralPaperNativeSourceRates.accuracy x)^3=2^(3*x.k) := by
    simp only [GeneralPaperNativeSourceRates.accuracy,←pow_mul,Nat.mul_comm x.k 3]
  have h := hA x
  simpa only [monomial,pow_zero,Nat.mul_one,GeneralPaperNativeSourceRates.fields,he,Nat.mul_assoc] using h

end Blotto.GeneralPaperBasisStorageRates
