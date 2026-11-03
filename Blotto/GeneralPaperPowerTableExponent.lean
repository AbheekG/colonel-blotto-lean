import Blotto.GeneralPaperCenteredExponent

/-! Sharp signed-exponent bounds for each stored power and every table
construction prefix. Each degree consumes at most one centered exponent
unit; no factor of the mantissa precision appears in that debt.
-/
namespace Blotto.GeneralPaperPowerTableExponent
open GeneralPaperDyadicFloat GeneralPaperRoundedPowerTable GeneralPaperCenteredExponent
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

theorem build (unit p : ℕ) (hUnit : 1<unit) (hPower : unit=2^p) (base : Number)
    (hNormal : Normal unit base) (hPositive : 0<base.mantissa) (hBase : centered p base=-1) (columns : ℕ) :
    Power p (GeneralPaperRoundedPowerTable.build unit p base columns).top.degree
      (GeneralPaperRoundedPowerTable.build unit p base columns).top.number ∧
      ∀ e∈(GeneralPaperRoundedPowerTable.build unit p base columns).entries,Power p e.degree e.number := by
  have hb : Power p 1 base := by unfold Power; rw [hBase]; norm_num
  induction columns with
  | zero => exact ⟨hb,by intro e he; cases he⟩
  | succ columns ih =>
    let previous := GeneralPaperRoundedPowerTable.build unit p base columns
    have hp := (build_good unit p hUnit hPower base hNormal hPositive columns).1.2.2.1
    have hNext : Power p (if columns=0 then 1 else 2*previous.top.degree)
        (if columns=0 then base else (GeneralPaperDyadicMultiply.multiply unit p previous.top.number previous.top.number).number) := by
      by_cases hc : columns=0
      · simpa only [hc,ite_true] using hb
      · simp only [hc,ite_false]
        simpa only [two_mul] using power_multiply unit p previous.top.degree previous.top.degree previous.top.number previous.top.number hp hp ih.1 ih.1
    have hn : Power p (GeneralPaperRoundedPowerTable.build unit p base (columns+1)).top.degree
        (GeneralPaperRoundedPowerTable.build unit p base (columns+1)).top.number := by
      by_cases hc : columns=0
      · simpa only [GeneralPaperRoundedPowerTable.build,hc,ite_true] using hb
      · simpa only [GeneralPaperRoundedPowerTable.build,square,hc,ite_false,previous] using hNext
    refine ⟨hn,?_⟩
    intro e he
    change e∈(GeneralPaperRoundedPowerTable.build unit p base (columns+1)).top::previous.entries at he
    rcases List.mem_cons.mp he with he|he
    · subst e; exact hn
    · exact ih.2 e he

theorem entries_degree_le_top (unit p columns : ℕ) (base : Number) :
    ∀ e∈(GeneralPaperRoundedPowerTable.build unit p base columns).entries,
      e.degree≤(GeneralPaperRoundedPowerTable.build unit p base columns).top.degree := by
  induction columns with
  | zero => intro e he; cases he
  | succ columns ih =>
    intro e he
    change e∈(GeneralPaperRoundedPowerTable.build unit p base (columns+1)).top::
      (GeneralPaperRoundedPowerTable.build unit p base columns).entries at he
    rcases List.mem_cons.mp he with he|he
    · subst e; exact Nat.le_refl _
    · have hi := ih e he
      cases columns with
      | zero => cases he
      | succ n =>
        change e.degree≤2*(GeneralPaperRoundedPowerTable.build unit p base (n+1)).top.degree
        omega

theorem level_positive (lambda k : ℕ) : 0<GeneralPaperPowerPrecision.levelBound lambda k := by
  have hr := GeneralPaperTrajectoryParameters.rows_positive lambda k
  have hm := GeneralPaperSourceParameters.mesh_positive k
  unfold GeneralPaperPowerPrecision.levelBound
  positivity

theorem prefix_degree_cap (lambda k columns : ℕ)
    (hColumns : columns≤(GeneralPaperPowerPrecision.prepare lambda k).columns) :
    let f := GeneralPaperPowerPrecision.prepare lambda k
    let b := (GeneralPaperStoredGeometricBase.construct f.unit f.fractionalBits k).number
    (GeneralPaperRoundedPowerTable.build f.unit f.fractionalBits b columns).top.degree≤GeneralPaperPowerPrecision.levelBound lambda k := by
  let f := GeneralPaperPowerPrecision.prepare lambda k
  let b := (GeneralPaperStoredGeometricBase.construct f.unit f.fractionalBits k).number
  let G := GeneralPaperPowerPrecision.levelBound lambda k
  have hG := level_positive lambda k
  have hCeiling := GeneralPaperPowerCeiling.ceiling_upper (G+1) (by omega)
  rw [GeneralPaperPowerCeiling.ceiling_power] at hCeiling
  change 2^f.columns<2*(G+1) at hCeiling
  change (GeneralPaperRoundedPowerTable.build f.unit f.fractionalBits b columns).top.degree≤G
  cases columns with
  | zero => change 1≤G; omega
  | succ columns =>
    rw [GeneralPaperRoundedPowerTable.top_degree]
    have hp := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hColumns
    change 2^(columns+1)≤2^f.columns at hp
    rw [pow_succ] at hp
    omega

theorem prefix_exponents (lambda k columns : ℕ)
    (hColumns : columns≤(GeneralPaperPowerPrecision.prepare lambda k).columns) :
    let f := GeneralPaperPowerPrecision.prepare lambda k
    let b := (GeneralPaperStoredGeometricBase.construct f.unit f.fractionalBits k).number
    let table := GeneralPaperRoundedPowerTable.build f.unit f.fractionalBits b columns
    table.top.number.exponent.natAbs≤GeneralPaperPowerPrecision.levelBound lambda k+f.fractionalBits ∧
      ∀ e∈table.entries,e.number.exponent.natAbs≤GeneralPaperPowerPrecision.levelBound lambda k+f.fractionalBits := by
  let f := GeneralPaperPowerPrecision.prepare lambda k
  let b := (GeneralPaperStoredGeometricBase.construct f.unit f.fractionalBits k).number
  have hu := GeneralPaperPowerPrecision.unit_positive lambda k
  have hn := GeneralPaperStoredGeometricBase.construct_normal f.unit f.fractionalBits k
    (Nat.zero_lt_of_lt hu) (GeneralPaperPowerPrecision.unit_power lambda k)
  have hs := build f.unit f.fractionalBits hu (GeneralPaperPowerPrecision.unit_power lambda k) b hn.1 hn.2
    (stored_base f.unit f.fractionalBits k) columns
  have hd := prefix_degree_cap lambda k columns hColumns
  constructor
  · exact (absolute_bound f.fractionalBits _ _ hs.1.1 (hs.1.2.trans (by decide))).trans (Nat.add_le_add_right hd _)
  · intro e he
    have hh := hs.2 e he
    have heDegree := (entries_degree_le_top f.unit f.fractionalBits columns b e he).trans hd
    exact (absolute_bound f.fractionalBits e.degree e.number hh.1 (hh.2.trans (by decide))).trans (Nat.add_le_add_right heDegree _)

end Blotto.GeneralPaperPowerTableExponent
