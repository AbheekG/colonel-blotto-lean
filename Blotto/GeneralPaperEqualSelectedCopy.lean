import Blotto.GeneralPaperEqualSamplerCopy

/-! Actual mixed-width copy for the selected returned closure. Pure rows
and the outer record use the stored outer address; grouped internals use
their own stored address. Every source load is priced at S. -/
namespace Blotto.GeneralPaperEqualSelectedCopy
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem row_ext {n : ℕ} (a b : RationalResourceArray n) (h : a.data = b.data) : a = b := by
  rcases a with ⟨a,ha⟩
  rcases b with ⟨b,hb⟩
  dsimp only at h
  subst b
  rfl

def row {n : ℕ} (S A : ℕ) (source : RationalResourceArray n) :=
  let actual := GeneralPaperScalarTableCopy.run S A rationalWordWidth (⟨source.data,source.size⟩ : FixedArrayTable n ℚ)
  ((⟨actual.1.data,actual.1.size⟩ : RationalResourceArray n),actual.2 + 64 * (S + A + 1))

theorem row_data {n : ℕ} (S A : ℕ) (source : RationalResourceArray n) : (row S A source).1 = source := by
  apply row_ext
  exact congrArg FixedArrayTable.data (GeneralPaperScalarTableCopy.data S A rationalWordWidth
    (⟨source.data,source.size⟩ : FixedArrayTable n ℚ))

def branch {n : ℕ} (S A : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} :
    GeneralPaperEqualBitBranch.Prepared v k budget → GeneralPaperEqualBitBranch.Prepared v k budget × ℕ
  | .dominant chosen heavy source correct =>
    let copied := row S A source
    let label := GeneralPaperReferenceCopy.scalar S A (fun j : Fin n => natBits j.val) chosen
    (.dominant label.1 heavy copied.1 (by rw [row_data]; exact correct),
      copied.2 + label.2 + 64 * (S + A + 1))
  | .grouped small sampler hK hB =>
    let copied := GeneralPaperEqualSamplerCopy.run S sampler.address sampler
    (.grouped small copied.1 (by rw [GeneralPaperEqualSamplerCopy.data]; exact hK)
      (by rw [GeneralPaperEqualSamplerCopy.data]; exact hB),copied.2 + 64 * (S + A + 1))

theorem branch_data {n : ℕ} (S A : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (source : GeneralPaperEqualBitBranch.Prepared v k budget) : (branch S A source).1 = source := by
  cases source <;> simp only [branch,row_data,GeneralPaperEqualSamplerCopy.data,GeneralPaperReferenceCopy.scalar]

theorem sampler_ext {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a b : Sampler v k budget) (h : a.branch = b.branch) (ha : a.address = b.address) : a = b := by
  rcases a with ⟨pa,aa,hA⟩
  rcases b with ⟨pb,ab,hB⟩
  dsimp only at h ha
  cases h
  cases ha
  rfl

def run {n : ℕ} (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (source : Sampler v k budget) :=
  let copied := branch S source.address source.branch
  let address := GeneralPaperReferenceCopy.scalar S source.address natBits source.address
  let actual : Sampler v k budget := ⟨copied.1,address.1,by rw [branch_data]; exact source.address_correct⟩
  (actual,copied.2 + address.2 + 64 * (S + source.address + 1))

theorem data {n : ℕ} (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (source : Sampler v k budget) :
    (run S source).1 = source := sampler_ext _ _ (branch_data S source.address source.branch) rfl

theorem branch_charged {n : ℕ} (S A : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (source : GeneralPaperEqualBitBranch.Prepared v k budget) :
    GeneralPaperEqualSelectedDescription.branchFootprint A (branch S A source).1 ≤ 128 * (branch S A source).2 := by
  cases source with
  | dominant chosen heavy source correct =>
    have h := GeneralPaperScalarTableCopy.charged S A rationalWordWidth
      (⟨source.data,source.size⟩ : FixedArrayTable n ℚ)
    dsimp only [branch,row,GeneralPaperEqualSelectedDescription.branchFootprint,GeneralPaperReferenceCopy.scalar]
    change arrayFootprint A rationalWordWidth
      (GeneralPaperScalarTableCopy.run S A rationalWordWidth (⟨source.data,source.size⟩ : FixedArrayTable n ℚ)).1 +
      natBits chosen.val + 32 * A ≤ _
    nlinarith
  | grouped small sampler hK hB =>
    have h := GeneralPaperEqualSamplerCopy.charged S sampler.address sampler
    dsimp only [branch,GeneralPaperEqualSelectedDescription.branchFootprint]
    change GeneralPaperEqualRetainedStorage.footprint sampler.address
      (GeneralPaperEqualSamplerCopy.run S sampler.address sampler).1 ≤ _
    nlinarith

theorem charged {n : ℕ} (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (source : Sampler v k budget) :
    GeneralPaperEqualSelectedDescription.footprint (run S source).1 ≤ 128 * (run S source).2 := by
  have h := branch_charged S source.address source.branch
  have hh : GeneralPaperEqualSelectedDescription.header source.address = natBits source.address + 97 * source.address := by
    simp only [GeneralPaperEqualSelectedDescription.header,fields,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      List.length_cons,List.length_nil]
    ring
  dsimp only [run,GeneralPaperEqualSelectedDescription.footprint,GeneralPaperReferenceCopy.scalar]
  rw [hh]
  nlinarith

end Blotto.GeneralPaperEqualSelectedCopy
