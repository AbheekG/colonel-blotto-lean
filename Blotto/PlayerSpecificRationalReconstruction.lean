import Blotto.PlayerSpecificNormalizedRoots

/-! Executable all-sign rational-root reconstruction in a refined affine
dyadic leaf. The actual CF query is followed by exact substitution and the
leaf's half-open containment test, including equality at its right end. -/
namespace Blotto.PlayerSpecificRationalReconstruction
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRootCells
set_option autoImplicit false
set_option maxHeartbeats 5000000

def decode (M : ℕ) (f : Farey.Fraction) : ℚ := 2*(M:ℚ)*f.value-(M:ℚ)

def run (p : Data) (M k D : ℕ) (node : Interval) : Option ℚ :=
  let found:=GeneralPaperProxyRootQuery.lookup D (2^k) (index M (2^k) node) (k+3)
  found.fraction.bind (fun f =>
    let q:=decode M f
    if node.lo<q ∧ q≤node.hi ∧ evaluate p q=0 then some q else none)

theorem sound (p : Data) (M k D : ℕ) (node : Interval) (q : ℚ) (h : run p M k D node=some q) :
    node.lo<q ∧ q≤node.hi ∧ evaluate p q=0 := by
  unfold run at h
  cases hf : (GeneralPaperProxyRootQuery.lookup D (2^k) (index M (2^k) node) (k+3)).fraction with
  | none => simp only [hf,Option.bind_none,reduceCtorEq] at h
  | some f =>
    simp only [hf,Option.bind_some] at h
    split at h
    · rename_i hvalid
      have he:=Option.some.inj h
      subst q
      exact hvalid
    · cases h

theorem decode_normalized (M : ℕ) (hM : 0<M) (q : ℚ) : 2*(M:ℚ)*normalized M q-(M:ℚ)=q := by
  have hMq : (M:ℚ)≠0 := by exact_mod_cast hM.ne'
  unfold normalized
  field_simp
  ring

theorem complete (p : Data) (M k D t : ℕ) (node : Interval) (hM : 0<M) (hD : 0<D)
    (hcell : Cell M k t node) (hscale : 4*D*D≤2^k) (q : ℚ)
    (hden : (normalized M q).den≤D) (hq : node.lo<q ∧ q≤node.hi ∧ evaluate p q=0) :
    run p M k D node=some q := by
  have hclosed:=PlayerSpecificNormalizedRoots.contains_closed M k t node hM hcell q ⟨hq.1.le,hq.2.1⟩
  have hnonneg : 0≤normalized M q := by
    have hl : (0:ℚ)≤GeneralPaperBucketGeometry.lower (2^k) t := by
      unfold GeneralPaperBucketGeometry.lower
      positivity
    exact hl.trans hclosed.1
  let target:=Farey.fractionOfRat (normalized M q)
  have hvalue : target.value=normalized M q := Farey.fractionOfRat_value _ hnonneg
  have ht : t<2^k := hcell.1
  have hpower : 8*2^k=2^(k+3) := by rw [pow_add]; norm_num; ring
  obtain ⟨found,hfound,hval⟩:=GeneralPaperProxyRootQuery.complete D (2^k) t (k+3) hD (Nat.two_pow_pos _) ht hscale hpower
    target hden (by rw [hvalue]; exact hclosed)
  have hdecode : decode M found=q := by
    rw [decode,hval,hvalue]
    exact decode_normalized M hM q
  unfold run
  dsimp only
  rw [index_value M k t node hM hcell,hfound]
  simp only [Option.bind_some,hdecode]
  exact ite_eq_left hq

end Blotto.PlayerSpecificRationalReconstruction
