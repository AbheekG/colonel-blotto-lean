import Blotto.GeneralPaperRealSegmentCompiler

/-! The actual stored group size selects the constant-size pair/triple
formula. Its fields are loaded once into a real-model environment and all
weights/endpoints are evaluated once, including zero-weight slots. -/
namespace Blotto.GeneralPaperEqualRealSegmentFactory
open GeneralPaperRealSegmentCompiler
set_option autoImplicit false
set_option maxHeartbeats 1600000

def pair (B : ℚ) : PreparedSegmentDescriptor (GeneralPaperPairSegmentPreparation.lottery B) × ℕ :=
  let env := PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun _ : Fin 1 => (B, 8))
  let h : ∀ j, env.1.read j = B := by rw [PaperIndexedArrayConstruction.run_data]; exact FixedArrayTable.read_ofFn _
  let compiled := run env.1 (GeneralPaperPairSegmentPreparation.programs B env.1 h)
  (compiled.1, env.2 + compiled.2 + 128)

def tripleEnvironment (i : RationalThreeSpec) : FixedArrayTable 5 ℚ × ℕ :=
  PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun j => (![i.B, i.a, i.d, i.c, i.p] j, 8))

theorem triple_environment (i : RationalThreeSpec) :
    (tripleEnvironment i).1 = RationalThreeSpecCode.environment i := by
  rw [tripleEnvironment, PaperIndexedArrayConstruction.run_data]
  rfl

def triple (i : RationalThreeSpec) : PreparedSegmentDescriptor i.segmentLottery × ℕ :=
  let env := tripleEnvironment i
  let compiled := run env.1 (GeneralPaperThreeSegmentPreparation.programs i env.1 (triple_environment i))
  (compiled.1, env.2 + compiled.2 + 128)

theorem pair_work (B : ℚ) : (pair B).2 ≤ 2097152 := by
  have hEnv := array_work (fun _ : Fin 1 => (B, 8)) 8 (fun _ => le_rfl)
  have hw (slot : Fin 9) : (GeneralPaperPairSegmentPreparation.weight slot).operationBound ≤ 2048 := by
    change 1 ≤ 2048; decide
  have hp (slot : Fin 9) (j : Fin 2) : (GeneralPaperPairSegmentPreparation.left slot j).operationBound ≤ 2048 := by
    fin_cases j <;> change 1 ≤ 2048 <;> decide
  have hq (slot : Fin 9) (j : Fin 2) : (GeneralPaperPairSegmentPreparation.right slot j).operationBound ≤ 2048 := by
    fin_cases j <;> change 1 ≤ 2048 <;> decide
  have h := work _ (GeneralPaperPairSegmentPreparation.programs B
    (PaperIndexedArrayConstruction.run (fun _ => 1) 1 (fun _ : Fin 1 => (B, 8))).1
    (by rw [PaperIndexedArrayConstruction.run_data]; exact FixedArrayTable.read_ofFn _)) 2048 hw hp hq
  norm_num [bound] at h
  unfold pair
  dsimp only
  omega

theorem triple_work (i : RationalThreeSpec) : (triple i).2 ≤ 2097152 := by
  have hEnv := array_work (fun j : Fin 5 => (![i.B, i.a, i.d, i.c, i.p] j, 8)) 8 (fun _ => le_rfl)
  have h := work _ (GeneralPaperThreeSegmentPreparation.programs i (tripleEnvironment i).1 (triple_environment i))
    2048 GeneralPaperThreeStaticPrograms.weight_operations GeneralPaperThreeStaticPrograms.left_operations
    GeneralPaperThreeStaticPrograms.right_operations
  norm_num [bound] at h
  unfold triple tripleEnvironment
  dsimp only [tripleEnvironment] at h
  dsimp only
  omega

def pairCase {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3) (h2 : m = 2) :
    PreparedSegmentDescriptor (i.lottery hm) × ℕ := by
  subst m
  exact pair i.B

def tripleCase {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3) (h3 : m = 3) :
    PreparedSegmentDescriptor (i.lottery hm) × ℕ := by
  subst m
  exact triple i.threeInput

theorem pairCase_work {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3) (h2 : m = 2) :
    (pairCase i hm h2).2 ≤ 2097152 := by
  subst m
  exact pair_work i.B

theorem tripleCase_work {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3) (h3 : m = 3) :
    (tripleCase i hm h3).2 ≤ 2097152 := by
  subst m
  exact triple_work i.threeInput

def prepare {m : ℕ} (i : RationalUniformGroupSpec m) (size : ℕ) (hSize : size = m) (hm : m = 2 ∨ m = 3) :
    PreparedSegmentDescriptor (i.lottery hm) × ℕ :=
  if h2 : size = 2 then
    let actual := pairCase i hm (hSize.symm.trans h2)
    (actual.1, actual.2 + 64)
  else
    let actual := tripleCase i hm (hm.resolve_left (fun h => h2 (hSize.trans h)))
    (actual.1, actual.2 + 64)

theorem prepare_data {m : ℕ} (i : RationalUniformGroupSpec m) (size : ℕ) (hSize : size = m) (hm : m = 2 ∨ m = 3) :
    (prepare i size hSize hm).1 = PreparedSegmentDescriptor.prepare (i.lottery hm) :=
  GeneralPaperSegmentExpressionCompiler.unique _ _

theorem prepare_work {m : ℕ} (i : RationalUniformGroupSpec m) (size : ℕ) (hSize : size = m) (hm : m = 2 ∨ m = 3) :
    (prepare i size hSize hm).2 ≤ 2097216 := by
  unfold prepare
  split
  · rename_i h2
    exact Nat.add_le_add_right (pairCase_work i hm (hSize.symm.trans h2)) 64
  · rename_i h2
    exact Nat.add_le_add_right (tripleCase_work i hm (hm.resolve_left (fun h => h2 (hSize.trans h)))) 64

end Blotto.GeneralPaperEqualRealSegmentFactory
