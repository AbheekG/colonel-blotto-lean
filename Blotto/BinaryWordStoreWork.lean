import Blotto.BinaryWordStoreLifetime

/-! Measured Boolean preparation of the physical seed tree. Each work counter
is accumulated by the producer that returns the next counter or seed suffix.
The old visit formula is used only to prove the closed linear bound. -/
namespace Blotto.BinaryWordStoreWork
open BinarySeedLookupTree BinaryWordStoreLifetime

def carryWithWork : List Bool → List Bool × ℕ
  | [] => ([true], 4)
  | false::rest => (true::rest, 4)
  | true::rest =>
      let later := carryWithWork rest
      (false::later.1, later.2+4)

theorem carry_state (bits : List Bool) :
    (carryWithWork bits).1 = (carryWithTrace bits).1 := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => cases bit <;> simp only [carryWithWork,carryWithTrace,ih]

theorem carry_work (bits : List Bool) :
    (carryWithWork bits).2 = 4*BinaryCarryCounter.carryCells bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      cases bit
      · rfl
      · simp only [carryWithWork,BinaryCarryCounter.carryCells,ih]
        omega

def countWithWork {α : Type*} : List α → List Bool → List Bool × ℕ
  | [],counter => (counter,2)
  | _::rest,counter =>
      let advanced := carryWithWork counter
      let later := countWithWork rest advanced.1
      (later.1,advanced.2+later.2+1)

theorem count_state {α : Type*} (items : List α) (counter : List Bool) :
    (countWithWork items counter).1 = (countWithTrace items counter).1 := by
  induction items generalizing counter with
  | nil => rfl
  | cons item rest ih =>
      simp only [countWithWork,countWithTrace,carry_state,ih]

theorem count_work {α : Type*} (items : List α) (counter : List Bool) :
    (countWithWork items counter).2 =
      4*BinaryCarryCounter.countCarryCells items counter+items.length+2 := by
  induction items generalizing counter with
  | nil => rfl
  | cons item rest ih =>
      simp only [countWithWork,carry_work,carry_state,carryWithTrace_erases,
        BinaryCarryCounter.countCarryCells,List.length_cons,ih]
      omega

def buildWithWork : (ruler : List Bool) → List Bool →
    (Tree ruler.length × List Bool) × ℕ
  | [],[] => ((.leaf false,[]),6)
  | [],bit::rest => ((.leaf bit,rest),6)
  | _::ruler,seed =>
      let left := buildWithWork ruler seed
      let right := buildWithWork ruler left.1.2
      ((.branch left.1.1 right.1.1,right.1.2),left.2+right.2+6)

theorem build_state (ruler seed : List Bool) :
    (buildWithWork ruler seed).1 = (buildWithTrace ruler seed).1 := by
  induction ruler generalizing seed with
  | nil => cases seed <;> rfl
  | cons bit rest ih =>
      simp only [buildWithWork,buildWithTrace,ih]

theorem build_work (ruler seed : List Bool) :
    (buildWithWork ruler seed).2 = 6*buildVisits ruler seed := by
  induction ruler generalizing seed with
  | nil => cases seed <;> rfl
  | cons bit rest ih =>
      simp only [buildWithWork,buildVisits,ih,build_state,buildWithTrace_erases]
      omega

def prepareWithWork (seed : List Bool) : Store × ℕ :=
  let ruler := countWithWork seed []
  let built := buildWithWork ruler.1 seed
  (⟨ruler.1.length,⟨ruler.1,rfl⟩,built.1.1⟩,ruler.2+built.2+ruler.1.length+4)

private def packStore (ruler : List Bool) (tree : Tree ruler.length) : Store :=
  ⟨ruler.length,⟨ruler,rfl⟩,tree⟩

theorem prepare_state (seed : List Bool) :
    (prepareWithWork seed).1 = (prepareWithTrace seed).1 := by
  change packStore (countWithWork seed []).1
      (buildWithWork (countWithWork seed []).1 seed).1.1 =
    packStore (countWithTrace seed []).1
      (buildWithTrace (countWithTrace seed []).1 seed).1.1
  rw [build_state,count_state]

theorem prepare_work_exact (seed : List Bool) :
    (prepareWithWork seed).2 = BinarySeedLookupTree.preparationCells seed+6+
      (countWithWork seed []).1.length := by
  simp only [prepareWithWork,count_work,build_work,count_state,countWithTrace_erases]
  unfold BinarySeedLookupTree.preparationCells
  omega

theorem prepare_work (seed : List Bool) :
    (prepareWithWork seed).2 ≤ 34*seed.length+13 := by
  rw [prepare_work_exact]
  have h := BinarySeedLookupTree.preparationCells_bound seed
  have hWidth : (countWithWork seed []).1.length ≤ binaryWordWidth seed.length := by
    rw [count_state,countWithTrace_erases]
    exact BinarySeedLookupTree.prepare_width_bound seed
  have hLinear : binaryWordWidth seed.length ≤ seed.length+1 := by
    unfold binaryWordWidth
    exact Nat.add_le_add_right (Nat.log2_le_self seed.length) 1
  omega

end Blotto.BinaryWordStoreWork
