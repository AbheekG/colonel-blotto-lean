import Blotto.GeneralPaperMeasuredPlanLifetimeRates

/-! Additive ownership of every actual indexed prefix, together with full
saved callback/partial/loop prices and control scratch. One prefix buffer
is shared through pending activations in the paper array model. -/
namespace Blotto.GeneralPaperMeasuredIndexedArrayLifetime
open GeneralPaperIndexedArrayLifetime (prefixTable prefix_data)
open GeneralPaperEncodedBasisStorage (arrayFootprint)
open GeneralPaperEncodedScalarStorage
open GeneralPaperMeasuredPlanLifetimeAlgebra
open GeneralPaperPayloadInstallationLifetime (cap)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem prefix_step {α : Type*} {n : ℕ} (S : ℕ) (callback : Fin n → α × ℕ) (code : α → ℕ)
    (k : ℕ) (hk : k + 1 ≤ n) :
    arrayFootprint S code (prefixTable id S callback (k + 1) hk) =
      arrayFootprint S code (prefixTable id S callback k (by omega)) + S + code (callback ⟨k,by omega⟩).1 := by
  simp only [prefix_data,arrayFootprint,FixedArrayTable.read_ofFn,Fin.sum_univ_castSucc,Fin.val_castSucc,Fin.val_last]
  ring

theorem prefix_mono {α : Type*} {n : ℕ} (S : ℕ) (callback : Fin n → α × ℕ) (code : α → ℕ)
    (i j : ℕ) (hi : i ≤ n) (hj : j ≤ n) (hij : i ≤ j) :
    arrayFootprint S code (prefixTable id S callback i hi) ≤ arrayFootprint S code (prefixTable id S callback j hj) := by
  induction j generalizing i with
  | zero =>
    have he : i = 0 := by omega
    subst i
    exact le_rfl
  | succ j ih =>
    by_cases he : i = j + 1
    · subst i; exact le_rfl
    · have h := ih i hi (by omega) (by omega)
      rw [prefix_step S callback code j hj]
      omega

theorem prefix_additive {α : Type*} {n : ℕ} (S : ℕ) (callback : Fin n → α × ℕ) (code : α → ℕ)
    (k : ℕ) (hk : k ≤ n) :
    arrayFootprint S code (prefixTable id S callback k hk) ≤ 64 * S + (∑ j : Fin n,(S + code (callback j).1)) := by
  simpa only [prefix_data,arrayFootprint,FixedArrayTable.read_ofFn] using prefix_mono S callback code k n hk le_rfl hk

def controls {α : Type*} {n : ℕ} (S : ℕ) (callback : Fin n → α × ℕ) (j : Fin n) : List ℕ :=
  let earlier := PaperIndexedArrayConstruction.fill id S callback j.val (Nat.le_of_lt j.isLt)
  let current := callback j
  let later := PaperIndexedArrayConstruction.fill id S callback (j.val + 1) (by omega)
  [S,n,j.val,earlier.2,current.2,PaperIndexedArrayConstruction.stepWork id S j.val,earlier.2 + current.2,later.2]

def frame {α : Type*} {n : ℕ} (S : ℕ) (callback : Fin n → α × ℕ) (j : Fin n) : ℕ :=
  fields S (controls S callback j) + PaperIndexedArrayConstruction.stepWork id S j.val + 128 * S

theorem frame_bound {α : Type*} {n : ℕ} (model : RationalCostModel) (S A Q : ℕ)
    (callback : Fin n → α × ℕ) (hWidth : binaryWordWidth (n + 1) ≤ A + 8)
    (hWork : (PaperIndexedArrayConstruction.run id S callback).2 ≤ Q) (j : Fin n) : frame S callback j ≤ unit model S A Q := by
  have hLater := (GeneralPaperIndexedArrayLifetime.fill_work_mono id S callback (j.val + 1) n (by omega) le_rfl (by omega)).trans hWork
  have hWhole := hLater
  change (PaperIndexedArrayConstruction.fill id S callback j.val (by omega)).2 + (callback j).2 +
    PaperIndexedArrayConstruction.stepWork id S j.val ≤ Q at hLater
  have hN := (binaryWordWidth_mono (show n ≤ n + 1 by omega)).trans hWidth
  have hJ := (binaryWordWidth_mono (show j.val ≤ n + 1 by omega)).trans hWidth
  have hStep := (binaryWordWidth_mono (show j.val + 1 ≤ n + 1 by omega)).trans hWidth
  have hFields := fields_bound S (A + 9 + natBits (cap S A Q)) (controls S callback j) (by
    intro x hx
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|hx
    · have h := Nat.add_le_add_left (binaryWordWidth_mono (show x ≤ cap x A Q by unfold cap; omega)) 1
      change natBits x ≤ natBits (cap x A Q) at h
      omega
    · unfold natBits; omega
    · unfold natBits; omega
    · have hp : x ≤ Q := by rcases hx with rfl|rfl|rfl|rfl|rfl <;> omega
      have h := price_word S A Q x hp
      omega)
  change fields S _ ≤ 8 * (A + 9 + natBits (cap S A Q) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S A Q
  unfold frame PaperIndexedArrayConstruction.stepWork
  dsimp only [id_eq]
  omega

def frames {α : Type*} {n : ℕ} (S : ℕ) (callback : Fin n → α × ℕ) : ℕ :=
  fields S [S,n,PaperIndexedArrayConstruction.initialWork id S n,(PaperIndexedArrayConstruction.run id S callback).2] +
    PaperIndexedArrayConstruction.initialWork id S n + 64 * S + ∑ j : Fin n,frame S callback j

theorem frames_bound {α : Type*} {n : ℕ} (model : RationalCostModel) (S A Q : ℕ)
    (callback : Fin n → α × ℕ) (hWidth : binaryWordWidth (n + 1) ≤ A + 8)
    (hWork : (PaperIndexedArrayConstruction.run id S callback).2 ≤ Q) : frames S callback ≤ (n + 1) * unit model S A Q := by
  have hInitial := (GeneralPaperIndexedArrayLifetime.fill_work_mono id S callback 0 n (by omega) le_rfl (by omega)).trans hWork
  change PaperIndexedArrayConstruction.initialWork id S n ≤ Q at hInitial
  have hFields := fields_bound S (A + 9 + natBits (cap S A Q))
    [S,n,PaperIndexedArrayConstruction.initialWork id S n,(PaperIndexedArrayConstruction.run id S callback).2] (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|hx
      · have h := Nat.add_le_add_left (binaryWordWidth_mono (show x ≤ cap x A Q by unfold cap; omega)) 1
        change natBits x ≤ natBits (cap x A Q) at h
        omega
      · have h := (binaryWordWidth_mono (show x ≤ x + 1 by omega)).trans hWidth
        unfold natBits; omega
      · have hp : x ≤ Q := by rcases hx with rfl|rfl <;> omega
        have h := price_word S A Q x hp
        omega)
  change fields S _ ≤ 4 * (A + 9 + natBits (cap S A Q) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S A Q
  have hInitialScratch : PaperIndexedArrayConstruction.initialWork id S n ≤ 4 * S + 2 * (A + 8) + 12 := by
    unfold PaperIndexedArrayConstruction.initialWork
    dsimp only [id_eq]
    omega
  have hBase : fields S [S,n,PaperIndexedArrayConstruction.initialWork id S n,(PaperIndexedArrayConstruction.run id S callback).2] +
      PaperIndexedArrayConstruction.initialWork id S n + 64 * S ≤ unit model S A Q := by omega
  have hSum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => frame_bound model S A Q callback hWidth hWork j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hSum
  unfold frames
  nlinarith only [hBase,hSum]

end Blotto.GeneralPaperMeasuredIndexedArrayLifetime
