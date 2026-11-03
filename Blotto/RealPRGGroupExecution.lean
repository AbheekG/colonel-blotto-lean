import Blotto.RealPRGReflectedExecution
import Blotto.RealUniformGroups
import Blotto.RealMixedGroups

/-! The low-dimensional caller reads actual cached totals and supplied retained
budget/mixture scalars. Its cached-size guard, scalar/record preparation, packet
materialization and selected native sampler have explicit named prices.
The data equalities below are mathematical readback certificates, not runtime
oracles. Neither grouping nor totals are recomputed by these callers. -/
namespace Blotto.RealPRGGroupExecution
open MeasureTheory PRGRealRAMExecution PRGExactRealRAMContract RealPRGNativeFactoryExecution RealPRGReflectedExecution
open scoped BigOperators Classical

noncomputable def scalar (address : ℕ) (value : ℝ) : Run ℝ := ⟨value,[.load address value]⟩

theorem scalar_cost (address : ℕ) (value : ℝ) : (scalar address value).cost = 1 := rfl

/-- The word-sized dimension is read from the cached array header. -/
noncomputable def groupGuard {m : ℕ} (totals : FixedArrayTable m ℝ) : Run Bool :=
  ⟨decide (totals.data.size = 2),[.control,.control]⟩

theorem groupGuard_value {m : ℕ} (totals : FixedArrayTable m ℝ) :
    (groupGuard totals).value = decide (m = 2) := by simp [groupGuard,totals.size]

theorem groupGuard_cost {m : ℕ} (totals : FixedArrayTable m ℝ) : (groupGuard totals).cost = 2 := rfl

private theorem cachedTwo {m : ℕ} (totals : FixedArrayTable m ℝ)
    (hc : (groupGuard totals).value = true) : m = 2 := by
  simpa only [groupGuard_value,decide_eq_true_eq] using hc

private theorem cachedThree {m : ℕ} (totals : FixedArrayTable m ℝ)
    (hm : m = 2 ∨ m = 3) (hc : ¬ (groupGuard totals).value = true) : m = 3 := by
  apply hm.resolve_left
  intro h2
  apply hc
  simp only [groupGuard_value,h2,decide_true]

theorem dropInputs_index (C D : ℕ) (seed : Fin (C + D) → ℝ) (j : Fin C) :
    RealUniformInputs.dropInputs C D seed j = seed ⟨D + j.val,by omega⟩ := by
  induction D with
  | zero =>
    change seed j = seed ⟨0 + j.val,by omega⟩
    apply congrArg seed
    apply Fin.ext
    change j.val = 0 + j.val
    omega
  | succ D ih =>
    change RealUniformInputs.dropInputs C D (Fin.tail seed) j = _
    rw [ih]
    change seed ⟨D + j.val + 1,by omega⟩ = seed ⟨D + 1 + j.val,by omega⟩
    apply congrArg seed
    apply Fin.ext
    change D + j.val + 1 = D + 1 + j.val
    omega

noncomputable def threePacket (seed : RealFourSeed) : Run (FixedArrayTable 9 ℝ) :=
  arrayRun 9 (fun j => ⟨seed.1 ⟨72 + j.val,by omega⟩,[.load (72 + j.val) (seed.1 ⟨72 + j.val,by omega⟩)]⟩)

theorem threePacket_value (seed : RealFourSeed) : (threePacket seed).value.read = realGroupThreeSeed seed := by
  funext j
  rw [show realGroupThreeSeed seed j = seed.1 ⟨72 + j.val,by omega⟩ from dropInputs_index 9 72 seed.1 j]
  exact arrayRun_read 9 _ j

theorem threePacket_cost (seed : RealFourSeed) : (threePacket seed).cost ≤ 29 :=
  arrayRun_bound 9 1 _ (fun _ => by rfl)

noncomputable def pairPoint (B : ℝ) (seed : RealFourSeed) : Run (FixedArrayTable 2 ℝ) :=
  let budget := scalar 0 B
  let u := uniform (realGroupUnit seed)
  let complement := arithmetic .sub 1 u.value
  let first := arithmetic .mul budget.value u.value
  let second := arithmetic .mul budget.value complement.value
  join budget (join u (join complement (join first (join second (copyRow ![first.value,second.value])))))

theorem pairPoint_value (B : ℝ) (seed : RealFourSeed) :
    (pairPoint B seed).value.read = complementaryPairPoint B (realGroupUnit seed) := by
  funext j
  simp [pairPoint,join_value,copyRow_read,scalar,uniform,arithmetic,Operation.realValue,RealArithmeticOp.apply,complementaryPairPoint]

theorem pairPoint_cost (B : ℝ) (seed : RealFourSeed) : (pairPoint B seed).cost ≤ 20 := by
  unfold pairPoint
  rw [join_cost,join_cost,join_cost,join_cost,join_cost,copyRow_cost]
  change 1 + (1 + (1 + (1 + (1 + 8)))) ≤ 20
  decide

noncomputable def storedThreeSpec (old : ThreeSpec) (fields : FixedArrayTable 5 ℝ)
    (h : fields.read = ![old.B,old.a,old.d,old.c,old.p]) : ThreeSpec where
  B := fields.read 0
  a := fields.read 1
  d := fields.read 2
  c := fields.read 3
  p := fields.read 4
  B_pos := by simpa [h] using old.B_pos
  a_pos := by simpa [h] using old.a_pos
  d_pos := by simpa [h] using old.d_pos
  c_pos := by simpa [h] using old.c_pos
  p_pos := by simpa [h] using old.p_pos
  a_le := by simpa [h] using old.a_le
  d_le := by simpa [h] using old.d_le
  c_le := by simpa [h] using old.c_le
  p_le := by simpa [h] using old.p_le
  balance := by simpa [h] using old.balance

theorem storedThreeSpec_value (old : ThreeSpec) (fields : FixedArrayTable 5 ℝ)
    (h : fields.read = ![old.B,old.a,old.d,old.c,old.p]) : storedThreeSpec old fields h = old := by
  apply ThreeSpec.eq_of_data
  · simp [storedThreeSpec,h]
  · simp [storedThreeSpec,h]
  · simp [storedThreeSpec,h]
  · simp [storedThreeSpec,h]
  · simp [storedThreeSpec,h]

noncomputable def uniformThreeInput (i : UniformGroupSpec 3) (totals : FixedArrayTable 3 ℝ)
    (hTotals : totals.read = i.length) (B : ℝ) (hB : B = i.B) : Run ThreeSpec :=
  let fields := arrayRun 5 (fun j =>
    (![scalar 0 B,loadReal totals 0,loadReal totals 1,loadReal totals 2,scalar 4 1] : Fin 5 → Run ℝ) j)
  have hFields : fields.value.read = ![i.threeInput.B,i.threeInput.a,i.threeInput.d,i.threeInput.c,i.threeInput.p] := by
    funext j
    fin_cases j <;> simp [fields,arrayRun_read,scalar,loadReal,Operation.realValue,hB,hTotals,UniformGroupSpec.threeInput]
  join fields ⟨storedThreeSpec i.threeInput fields.value hFields,
    [.storeCell 0,.storeCell 1,.storeCell 2,.storeCell 3,.storeCell 4,.control]⟩

theorem uniformThreeInput_value (i : UniformGroupSpec 3) (totals : FixedArrayTable 3 ℝ)
    (hTotals : totals.read = i.length) (B : ℝ) (hB : B = i.B) :
    (uniformThreeInput i totals hTotals B hB).value = i.threeInput := by
  simp only [uniformThreeInput,join_value,storedThreeSpec_value]

theorem uniformThreeInput_cost (i : UniformGroupSpec 3) (totals : FixedArrayTable 3 ℝ)
    (hTotals : totals.read = i.length) (B : ℝ) (hB : B = i.B) :
    (uniformThreeInput i totals hTotals B hB).cost ≤ 30 := by
  have hf := arrayRun_bound 5 1 (fun j =>
    (![scalar 0 B,loadReal totals 0,loadReal totals 1,loadReal totals 2,scalar 4 1] : Fin 5 → Run ℝ) j)
    (fun j => by fin_cases j <;> rfl)
  unfold uniformThreeInput
  rw [join_cost]
  change _ + 6 ≤ 30
  omega

noncomputable def uniformDraw {m : ℕ} (i : UniformGroupSpec m) (hm : m = 2 ∨ m = 3)
    (totals : FixedArrayTable m ℝ) (hTotals : totals.read = i.length) (B : ℝ) (hB : B = i.B)
    (seed : RealFourSeed) : Run (FixedArrayTable m ℝ) := by
  let tested := groupGuard totals
  by_cases hc : tested.value = true
  · have h2 : m = 2 := cachedTwo totals hc
    subst m
    exact join tested (join (⟨(),[.control]⟩ : Run Unit) (pairPoint B seed))
  · have h3 : m = 3 := cachedThree totals hm hc
    subst m
    let prepared := uniformThreeInput i totals hTotals B hB
    let packet := threePacket seed
    exact join tested (join (⟨(),[.control]⟩ : Run Unit)
      (join prepared (join packet (threeDraw prepared.value packet.value.read))))

theorem uniformDraw_value {m : ℕ} (i : UniformGroupSpec m) (hm : m = 2 ∨ m = 3)
    (totals : FixedArrayTable m ℝ) (hTotals : totals.read = i.length) (B : ℝ) (hB : B = i.B) (seed : RealFourSeed) :
    (uniformDraw i hm totals hTotals B hB seed).value.read = i.realSample hm seed := by
  rcases hm with rfl | rfl
  · have hTest : (groupGuard totals).value = true := by rw [groupGuard_value]; decide
    unfold uniformDraw
    dsimp only
    simp only [dite_eq_left hTest,join_value]
    change (pairPoint B seed).value.read = complementaryPairPoint i.B (realGroupUnit seed)
    rw [pairPoint_value,hB]
  · have hTest : ¬ (groupGuard totals).value = true := by rw [groupGuard_value]; decide
    unfold uniformDraw
    dsimp only
    simp only [dite_eq_right hTest,join_value]
    change (threeDraw (uniformThreeInput i totals hTotals B hB).value (threePacket seed).value.read).value.read =
      i.threeInput.realSample (realGroupThreeSeed seed)
    rw [threeDraw_value,uniformThreeInput_value,threePacket_value]

theorem uniformDraw_cost {m : ℕ} (i : UniformGroupSpec m) (hm : m = 2 ∨ m = 3)
    (totals : FixedArrayTable m ℝ) (hTotals : totals.read = i.length) (B : ℝ) (hB : B = i.B) (seed : RealFourSeed) :
    (uniformDraw i hm totals hTotals B hB seed).cost ≤ 7200 := by
  rcases hm with rfl | rfl
  · have hTest : (groupGuard totals).value = true := by rw [groupGuard_value]; decide
    unfold uniformDraw
    dsimp only
    simp only [dite_eq_left hTest]
    change (join (groupGuard totals) (join (⟨(),[Operation.control]⟩ : Run Unit) (pairPoint B seed))).cost ≤ 7200
    rw [join_cost,join_cost,groupGuard_cost]
    change 2 + (1 + _) ≤ 7200
    have hp := pairPoint_cost B seed
    omega
  · have hTest : ¬ (groupGuard totals).value = true := by rw [groupGuard_value]; decide
    unfold uniformDraw
    dsimp only
    simp only [dite_eq_right hTest]
    change (join (groupGuard totals) (join (⟨(),[Operation.control]⟩ : Run Unit) (join (uniformThreeInput i totals hTotals B hB)
      (join (threePacket seed) (threeDraw (uniformThreeInput i totals hTotals B hB).value (threePacket seed).value.read))))).cost ≤ 7200
    rw [join_cost,join_cost,join_cost,join_cost,groupGuard_cost]
    change 2 + (1 + _) ≤ 7200
    have hi := uniformThreeInput_cost i totals hTotals B hB
    have hp := threePacket_cost seed
    have hd := threeDraw_cost (uniformThreeInput i totals hTotals B hB).value (threePacket seed).value.read
    omega

theorem uniformDraw_law {m : ℕ} (i : UniformGroupSpec m) (hm : m = 2 ∨ m = 3)
    (totals : FixedArrayTable m ℝ) (hTotals : totals.read = i.length) (B : ℝ) (hB : B = i.B) :
    Measure.map (fun seed => (uniformDraw i hm totals hTotals B hB seed).value.read)
      (FourInput.realInputLaw : Measure RealFourSeed) = (i.law hm : Measure (Allocation m)) := by
  have h : (fun seed => (uniformDraw i hm totals hTotals B hB seed).value.read) = i.realSample hm :=
    funext (uniformDraw_value i hm totals hTotals B hB)
  rw [h]
  exact i.realSample_law hm

theorem uniformDraw_fullBudget {m : ℕ} (i : UniformGroupSpec m) (hm : m = 2 ∨ m = 3)
    (totals : FixedArrayTable m ℝ) (hTotals : totals.read = i.length) (B : ℝ) (hB : B = i.B) (seed : RealFourSeed)
    (hs : realGroupSeedValid seed) : FullBudget B (uniformDraw i hm totals hTotals B hB seed).value.read := by
  rw [uniformDraw_value,hB]
  exact i.realSample_fullBudget hm seed hs

noncomputable def mixedThreeInput (i : MixedGroupSpec 2) (totals : FixedArrayTable 2 ℝ)
    (hTotals : totals.read = i.length) (B ell probability : ℝ)
    (hB : B = i.B) (hEll : ell = i.ell) (hP : probability = i.p) : Run ThreeSpec :=
  let fields := arrayRun 5 (fun j =>
    (![scalar 0 B,loadReal totals 0,loadReal totals 1,scalar 3 ell,scalar 4 probability] : Fin 5 → Run ℝ) j)
  have hFields : fields.value.read = ![i.threeInput.B,i.threeInput.a,i.threeInput.d,i.threeInput.c,i.threeInput.p] := by
    funext j
    fin_cases j <;> simp [fields,arrayRun_read,scalar,loadReal,Operation.realValue,hB,hEll,hP,hTotals,MixedGroupSpec.threeInput]
  join fields ⟨storedThreeSpec i.threeInput fields.value hFields,
    [.storeCell 0,.storeCell 1,.storeCell 2,.storeCell 3,.storeCell 4,.control]⟩

theorem mixedThreeInput_value (i : MixedGroupSpec 2) (totals : FixedArrayTable 2 ℝ)
    (hTotals : totals.read = i.length) (B ell probability : ℝ)
    (hB : B = i.B) (hEll : ell = i.ell) (hP : probability = i.p) :
    (mixedThreeInput i totals hTotals B ell probability hB hEll hP).value = i.threeInput := by
  simp only [mixedThreeInput,join_value,storedThreeSpec_value]

theorem mixedThreeInput_cost (i : MixedGroupSpec 2) (totals : FixedArrayTable 2 ℝ)
    (hTotals : totals.read = i.length) (B ell probability : ℝ)
    (hB : B = i.B) (hEll : ell = i.ell) (hP : probability = i.p) :
    (mixedThreeInput i totals hTotals B ell probability hB hEll hP).cost ≤ 30 := by
  have hf := arrayRun_bound 5 1 (fun j =>
    (![scalar 0 B,loadReal totals 0,loadReal totals 1,scalar 3 ell,scalar 4 probability] : Fin 5 → Run ℝ) j)
    (fun j => by fin_cases j <;> rfl)
  unfold mixedThreeInput
  rw [join_cost]
  change _ + 6 ≤ 30
  omega

theorem fourSpec_ext (s t : FourSpec) (hB : s.B = t.B) (hL : s.length = t.length)
    (hEll : s.ell = t.ell) (hP : s.p = t.p) : s = t := by
  cases s
  cases t
  cases hB
  cases hL
  cases hEll
  cases hP
  rfl

noncomputable def mixedFourInput (i : MixedGroupSpec 3) (totals : FixedArrayTable 3 ℝ)
    (hTotals : totals.read = i.length) (B ell probability : ℝ)
    (hB : B = i.B) (hEll : ell = i.ell) (hP : probability = i.p) : Run FourSpec :=
  let budget := scalar 0 B
  let lastLength := scalar 1 ell
  let mixture := scalar 2 probability
  let copied := arrayRun 3 (loadReal totals)
  have hCopied : copied.value.read = i.length := by
    funext j
    rw [arrayRun_read]
    change totals.read j = i.length j
    exact congrFun hTotals j
  let produced : FourSpec :=
    { B := budget.value
      length := copied.value.read
      ell := lastLength.value
      p := mixture.value
      length_pos := by rw [hCopied]; exact i.length_pos
      length_le := by rw [hCopied]; change ∀ j, i.length j ≤ B; rw [hB]; exact i.length_le
      ell_pos := by change 0 < ell; rw [hEll]; exact i.ell_pos
      ell_le := by change ell ≤ B; rw [hB,hEll]; exact i.ell_le
      p_pos := by change 0 < probability; rw [hP]; exact i.p_pos
      p_lt := by change probability < 1; rw [hP]; exact i.p_lt
      balance := by rw [hCopied]; change (∑ j, i.length j) + probability * ell = 2 * B; rw [hB,hEll,hP]; exact i.balance }
  join budget (join lastLength (join mixture (join copied
    ⟨produced,[.storeCell 0,.storeCell 1,.storeCell 2,.storeCell 3,.storeCell 4,.storeCell 5,.control]⟩)))

theorem mixedFourInput_value (i : MixedGroupSpec 3) (totals : FixedArrayTable 3 ℝ)
    (hTotals : totals.read = i.length) (B ell probability : ℝ)
    (hB : B = i.B) (hEll : ell = i.ell) (hP : probability = i.p) :
    (mixedFourInput i totals hTotals B ell probability hB hEll hP).value = i.fourInput := by
  apply fourSpec_ext
  · simp only [mixedFourInput,join_value,scalar,MixedGroupSpec.fourInput,hB]
  · funext j
    simp only [mixedFourInput,join_value,arrayRun_read,loadReal,Operation.realValue,MixedGroupSpec.fourInput]
    exact congrFun hTotals j
  · simp only [mixedFourInput,join_value,scalar,MixedGroupSpec.fourInput,hEll]
  · simp only [mixedFourInput,join_value,scalar,MixedGroupSpec.fourInput,hP]

theorem mixedFourInput_cost (i : MixedGroupSpec 3) (totals : FixedArrayTable 3 ℝ)
    (hTotals : totals.read = i.length) (B ell probability : ℝ)
    (hB : B = i.B) (hEll : ell = i.ell) (hP : probability = i.p) :
    (mixedFourInput i totals hTotals B ell probability hB hEll hP).cost ≤ 30 := by
  have hCopy := arrayRun_bound 3 1 (loadReal totals) (fun _ => by rfl)
  unfold mixedFourInput
  rw [join_cost,join_cost,join_cost,join_cost]
  simp only [scalar_cost]
  change 1 + (1 + (1 + (_ + 7))) ≤ 30
  omega

noncomputable def mixedDraw {m : ℕ} (i : MixedGroupSpec m) (hm : m = 2 ∨ m = 3)
    (totals : FixedArrayTable m ℝ) (hTotals : totals.read = i.length) (B ell probability : ℝ)
    (hB : B = i.B) (hEll : ell = i.ell) (hP : probability = i.p)
    (seed : RealFourSeed) : Run (FixedArrayTable (m + 1) ℝ) := by
  let tested := groupGuard totals
  by_cases hc : tested.value = true
  · have h2 : m = 2 := cachedTwo totals hc
    subst m
    let prepared := mixedThreeInput i totals hTotals B ell probability hB hEll hP
    let packet := threePacket seed
    exact join tested (join (⟨(),[.control]⟩ : Run Unit)
      (join prepared (join packet (threeDraw prepared.value packet.value.read))))
  · have h3 : m = 3 := cachedThree totals hm hc
    subst m
    let prepared := mixedFourInput i totals hTotals B ell probability hB hEll hP
    exact join tested (join (⟨(),[.control]⟩ : Run Unit) (join prepared (fourSpecDraw prepared.value seed)))

theorem mixedDraw_value {m : ℕ} (i : MixedGroupSpec m) (hm : m = 2 ∨ m = 3)
    (totals : FixedArrayTable m ℝ) (hTotals : totals.read = i.length) (B ell probability : ℝ)
    (hB : B = i.B) (hEll : ell = i.ell) (hP : probability = i.p) (seed : RealFourSeed) :
    (mixedDraw i hm totals hTotals B ell probability hB hEll hP seed).value.read = i.realSample hm seed := by
  rcases hm with rfl | rfl
  · have hTest : (groupGuard totals).value = true := by rw [groupGuard_value]; decide
    unfold mixedDraw
    dsimp only
    simp only [dite_eq_left hTest,join_value]
    change (threeDraw (mixedThreeInput i totals hTotals B ell probability hB hEll hP).value (threePacket seed).value.read).value.read =
      i.threeInput.realSample (realGroupThreeSeed seed)
    rw [threeDraw_value,mixedThreeInput_value,threePacket_value]
  · have hTest : ¬ (groupGuard totals).value = true := by rw [groupGuard_value]; decide
    unfold mixedDraw
    dsimp only
    simp only [dite_eq_right hTest,join_value]
    change (fourSpecDraw (mixedFourInput i totals hTotals B ell probability hB hEll hP).value seed).value.read =
      i.fourInput.realSample seed
    rw [fourSpecDraw_value,mixedFourInput_value]

theorem mixedDraw_cost {m : ℕ} (i : MixedGroupSpec m) (hm : m = 2 ∨ m = 3)
    (totals : FixedArrayTable m ℝ) (hTotals : totals.read = i.length) (B ell probability : ℝ)
    (hB : B = i.B) (hEll : ell = i.ell) (hP : probability = i.p) (seed : RealFourSeed) :
    (mixedDraw i hm totals hTotals B ell probability hB hEll hP seed).cost ≤ 428000 := by
  rcases hm with rfl | rfl
  · have hTest : (groupGuard totals).value = true := by rw [groupGuard_value]; decide
    unfold mixedDraw
    dsimp only
    simp only [dite_eq_left hTest]
    change (join (groupGuard totals) (join (⟨(),[Operation.control]⟩ : Run Unit) (join (mixedThreeInput i totals hTotals B ell probability hB hEll hP)
      (join (threePacket seed) (threeDraw (mixedThreeInput i totals hTotals B ell probability hB hEll hP).value (threePacket seed).value.read))))).cost ≤ 428000
    rw [join_cost,join_cost,join_cost,join_cost,groupGuard_cost]
    change 2 + (1 + _) ≤ 428000
    have hi := mixedThreeInput_cost i totals hTotals B ell probability hB hEll hP
    have hp := threePacket_cost seed
    have hd := threeDraw_cost (mixedThreeInput i totals hTotals B ell probability hB hEll hP).value (threePacket seed).value.read
    omega
  · have hTest : ¬ (groupGuard totals).value = true := by rw [groupGuard_value]; decide
    unfold mixedDraw
    dsimp only
    simp only [dite_eq_right hTest]
    change (join (groupGuard totals) (join (⟨(),[Operation.control]⟩ : Run Unit) (join (mixedFourInput i totals hTotals B ell probability hB hEll hP)
      (fourSpecDraw (mixedFourInput i totals hTotals B ell probability hB hEll hP).value seed)))).cost ≤ 428000
    rw [join_cost,join_cost,join_cost,groupGuard_cost]
    change 2 + (1 + _) ≤ 428000
    have hi := mixedFourInput_cost i totals hTotals B ell probability hB hEll hP
    have hd := fourSpecDraw_cost (mixedFourInput i totals hTotals B ell probability hB hEll hP).value seed
    omega

theorem mixedDraw_law {m : ℕ} (i : MixedGroupSpec m) (hm : m = 2 ∨ m = 3)
    (totals : FixedArrayTable m ℝ) (hTotals : totals.read = i.length) (B ell probability : ℝ)
    (hB : B = i.B) (hEll : ell = i.ell) (hP : probability = i.p) :
    Measure.map (fun seed => (mixedDraw i hm totals hTotals B ell probability hB hEll hP seed).value.read)
      (FourInput.realInputLaw : Measure RealFourSeed) = (i.law hm : Measure (Allocation (m + 1))) := by
  have h : (fun seed => (mixedDraw i hm totals hTotals B ell probability hB hEll hP seed).value.read) = i.realSample hm :=
    funext (mixedDraw_value i hm totals hTotals B ell probability hB hEll hP)
  rw [h]
  exact i.realSample_law hm

theorem mixedDraw_fullBudget {m : ℕ} (i : MixedGroupSpec m) (hm : m = 2 ∨ m = 3)
    (totals : FixedArrayTable m ℝ) (hTotals : totals.read = i.length) (B ell probability : ℝ)
    (hB : B = i.B) (hEll : ell = i.ell) (hP : probability = i.p) (seed : RealFourSeed)
    (hs : realGroupSeedValid seed) : FullBudget B (mixedDraw i hm totals hTotals B ell probability hB hEll hP seed).value.read := by
  rw [mixedDraw_value,hB]
  exact i.realSample_fullBudget hm seed hs

end Blotto.RealPRGGroupExecution
