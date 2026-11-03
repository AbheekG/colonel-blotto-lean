import Blotto.GeneralPaperEqualSelectedCopyComponents

/-! Exact outer selected-copy saved prices, including pure row-wrapper,
label and partial sums or the grouped child price/inner address. All values
are bounded by actual complete copy work and the stored outer reference. -/
namespace Blotto.GeneralPaperEqualSelectedCopyControls
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperEncodedScalarStorage
open GeneralPaperEqualBitDrawRates (log)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 8192

def branchControls {n : ℕ} (S A : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} :
    GeneralPaperEqualBitBranch.Prepared v k budget → List ℕ
  | .dominant chosen _ row _ =>
    let raw := (GeneralPaperScalarTableCopy.run S A rationalWordWidth (GeneralPaperEqualPureCopyLifetime.table row)).2
    let copied := (GeneralPaperEqualSelectedCopy.row S A row).2
    let label := natBits chosen.val + 32 * (S + A + 1)
    [raw,copied,label,copied+label]
  | .grouped _ sampler _ _ => [sampler.address,(GeneralPaperEqualSamplerCopy.run S sampler.address sampler).2]

def controls {n : ℕ} (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (a : Sampler v k budget) : List ℕ :=
  let branch := (GeneralPaperEqualSelectedCopy.branch S a.address a.branch).2
  let address := natBits a.address + 32 * (S + a.address + 1)
  branchControls S a.address a.branch ++ [n,S,a.address,branch,address,branch+address,
    (GeneralPaperEqualSelectedCopy.run S a).2,64 * (S + a.address + 1)]

def cap (S n D C : ℕ) : ℕ := C + n + S + D + 64 * (S + D + 1)

theorem length {n : ℕ} (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (a : Sampler v k budget) :
    (controls S a).length ≤ 12 := by
  cases a with
  | mk branch A hA =>
    cases branch with
    | dominant chosen heavy row correct => change 12 ≤ 12; omega
    | grouped small sampler hK hB => change 10 ≤ 12; omega

theorem values_le {n : ℕ} (S D C : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (a : Sampler v k budget) (hWork : (GeneralPaperEqualSelectedCopy.run S a).2 ≤ C) (hA : a.address ≤ D)
    (x : ℕ) (hx : x ∈ controls S a) : x ≤ cap S n D C := by
  cases a with
  | mk branch A hAddress =>
    dsimp only at hA
    cases branch with
    | dominant chosen heavy row correct =>
      dsimp only [controls,branchControls,GeneralPaperEqualSelectedCopy.run,GeneralPaperEqualSelectedCopy.branch,
        GeneralPaperEqualSelectedCopy.row,GeneralPaperReferenceCopy.scalar,GeneralPaperEqualPureCopyLifetime.table] at hx hWork
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold cap; omega
    | grouped small sampler hK hB =>
      change A = sampler.address + 1 at hAddress
      dsimp only [controls,branchControls,GeneralPaperEqualSelectedCopy.run,GeneralPaperEqualSelectedCopy.branch,
        GeneralPaperReferenceCopy.scalar] at hx hWork
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals unfold cap; omega

def parentCap (S n k b : ℕ) : ℕ := cap S n (2 * log n k b + 1) (GeneralPaperEqualSelectedCopyWork.profile S n k b)
def profile (S n k b : ℕ) : ℕ :=
  12 * (natBits (parentCap S n k b) + S) + 32 * S + 256 * (S + 2 * log n k b + 2)

def window {n : ℕ} (S : ℕ) {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (a : Sampler v k budget) : ℕ :=
  fields S (controls S a) + 256 * (S + a.address + 1)

theorem bounded {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    window S a ≤ profile S n k (rationalWordWidth budget) := by
  have hWork := GeneralPaperEqualSelectedCopyWork.work model W S k values v hv budget a
  have hA := GeneralPaperEqualSelectedSampler.address_bound a
  have hf := fields_bound S (natBits (parentCap S n k (rationalWordWidth budget))) (controls S a) (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    exact values_le S _ _ a hWork hA x hx)
  have hLength := Nat.mul_le_mul_right (natBits (parentCap S n k (rationalWordWidth budget)) + S) (length S a)
  dsimp only [window,profile]
  omega

end Blotto.GeneralPaperEqualSelectedCopyControls
