import checkpoints.shen_extension.ShellCycleSupply

namespace LeanCH.BR.PhysicalCycleStock
open Finset BRq2 BRq3 BR45 BRsGen

private theorem second_parent {D V u b} (hu : u ∈ V) (hb : b ∈ N2 D V u) :
    ∃ x ∈ outN D V u, D x b = true := by
  obtain ⟨x, hx, arc⟩ := ball_succ_pred hu (mem_N2.mp hb).1 (mem_N2.mp hb).2
  have near := ((mem_ball_one hu).mp hx).resolve_left (fun e => by
    subst x
    exact (mem_N2.mp hb).2 (ball_of_adj (N2_subV hb) arc))
  exact ⟨x, near, arc⟩

/-- If two roots use the same literal second-layer bank and the same third
layer, different extra second-layer labels force both ordered radius-three
holes. This needs only the layer identities and equal native row degrees. -/
theorem second_side_pairs {D V q r u v a b C Z} (free : QFree D V q) (hq : 4 ≤ q)
    (reg : OutEq r D V) (hu : u ∈ V) (hv : v ∈ V) (distinct : u ≠ v) (extras : a ≠ b)
    (awayA : a ∉ C) (awayB : b ∉ C)
    (secondU : N2 D V u = insert a C) (secondV : N2 D V v = insert b C)
    (thirdU : N3 D V u = Z) (thirdV : N3 D V v = Z) :
    v ∉ ball D V u 3 ∧ u ∉ ball D V v 3 := by
  have one {u v a b : ℕ} (hu : u ∈ V) (hv : v ∈ V) (distinct : u ≠ v) (extras : a ≠ b)
      (awayB : b ∉ C)
      (secondU : N2 D V u = insert a C) (secondV : N2 D V v = insert b C)
      (thirdU : N3 D V u = Z) (thirdV : N3 D V v = Z) : v ∉ ball D V u 3 := by
    let X := outN D V u
    have vmC : v ∉ C := fun hc =>
      (mem_N2.mp (secondV.symm ▸ mem_insert_of_mem hc)).2 (self_mem_ball hv)
    have vmZ : v ∉ Z := fun hz => (mem_N3.mp (thirdV.symm ▸ hz)).2 (self_mem_ball hv)
    have inX (w) (hw : w ∈ outN D V v) : w ∉ C ∧ w ∉ Z :=
      ⟨fun hc => (mem_N2.mp (secondV.symm ▸ mem_insert_of_mem hc)).2 (X_B1 hw),
       fun hz => (mem_N3.mp (thirdV.symm ▸ hz)).2
         (ball_mono_radius (by decide : 1 ≤ 2) (X_B1 hw))⟩
    intro reach
    have two : v ∈ ball D V u 2 := by
      by_contra no
      exact vmZ (thirdU ▸ mem_N3.mpr ⟨reach, no⟩)
    by_cases first : v ∈ ball D V u 1
    · have vx : v ∈ X := ((mem_ball_one hu).mp first).resolve_left (Ne.symm distinct)
      have stays : outN D V v ⊆ insert a (X.erase v) := by
        intro y hy
        have raw := hy
        rw [outN_X_eq (free.mono_bound hq) hu vx] at raw
        rcases mem_union.mp (outN_subset raw) with inFirst | inSecond
        · exact mem_insert_of_mem (mem_erase.mpr ⟨fun e =>
            loopfree free (by omega) hv (e ▸ (mem_outN.mp hy).2), inFirst⟩)
        · exact mem_insert.mpr ((mem_insert.mp (secondU ▸ inSecond)).elim Or.inl
            (fun hc => ((inX y hy).1 hc).elim))
      have ay : a ∈ N2 D V u := secondU.symm ▸ mem_insert_self a C
      have xa : a ∉ X := fun hit => (mem_N2.mp ay).2 (X_B1 hit)
      have eq : outN D V v = insert a (X.erase v) := by
        apply eq_of_subset_of_card_le stays
        rw [card_insert_of_notMem (fun h => xa (mem_of_mem_erase h)), card_erase_of_mem vx,
          reg v hv, show X.card=r from reg u hu]
        have hpos : 0 < r := by
          rw [← show X.card=r from reg u hu]
          exact card_pos.mpr ⟨v, vx⟩
        omega
      have by' : b ∈ N2 D V v := secondV.symm ▸ mem_insert_self b C
      have bV : b ∈ V := N2_subV by'
      have bx : b ∉ X := by
        intro hit
        by_cases ev : b = v
        · exact (mem_N2.mp by').2 (ev.symm ▸ self_mem_ball hv)
        · apply (mem_N2.mp by').2
          exact X_B1 (eq.symm ▸ mem_insert_of_mem (mem_erase.mpr ⟨ev, hit⟩))
      have bu : b ≠ u := fun e => by
        have rv := (mem_N2.mp by').1
        subst b
        exact no_back_arc free hv rv (by omega) (mem_outN.mp vx).2
      have bz : b ∉ Z := fun hit => (mem_N3.mp (thirdV.symm ▸ hit)).2 (mem_N2.mp by').1
      obtain ⟨x, hx, xb⟩ := second_parent hv by'
      have off2 : b ∉ ball D V u 2 := by
        intro hit
        by_cases early : b ∈ ball D V u 1
        · exact ((mem_ball_one hu).mp early).elim bu bx
        · exact ((mem_insert.mp (secondU ▸ mem_N2.mpr ⟨hit, early⟩))).elim (Ne.symm extras) awayB
      rcases mem_insert.mp (eq ▸ hx) with same | early
      · subst x
        exact bz (thirdU ▸ mem_N3.mpr ⟨ball_step (mem_N2.mp ay).1 bV xb, off2⟩)
      · exact off2 (ball_step (X_B1 (mem_of_mem_erase early)) bV xb)
    · have second := mem_N2.mpr ⟨two, first⟩
      have va : v = a := (mem_insert.mp (secondU ▸ second)).resolve_right vmC
      have stays : outN D V v ⊆ X := by
        intro y hy
        rcases headY (free.mono_bound hq) hu second (outN_subset hy) (mem_outN.mp hy).2 with early | far
        · rcases mem_union.mp early with xx | yy
          · exact xx
          · rcases mem_insert.mp (secondU ▸ yy) with ya | yc
            · have eq := ya.trans va.symm
              have loop : D v v = true := eq ▸ (mem_outN.mp hy).2
              exact (loopfree free (by omega) hv loop).elim
            · exact ((inX y hy).1 yc).elim
        · exact ((inX y hy).2 (thirdU ▸ far)).elim
      have eq : outN D V v = X :=
        eq_of_subset_of_card_le stays (by rw [reg v hv, show X.card=r from reg u hu])
      obtain ⟨x, hx, xv⟩ := second_parent hu second
      have hx' : x ∈ outN D V v := by rw [eq]; exact hx
      exact digonfree free (by omega) (outN_subset hx) hv xv (mem_outN.mp hx').2
  exact ⟨one hu hv distinct extras awayB secondU secondV thirdU thirdV,
    one hv hu distinct.symm extras.symm awayA secondV secondU thirdV thirdU⟩

/-- A direction between distinct first-layer origins cannot leave through
their common bank. If the extra first head is itself reached from the
target within budget, that head must be the target label itself. -/
theorem first_side_contact {D V q k t u v w C} (free : QFree D V q)
    (time : k+t ≤ q+1) (one : 1 ≤ t) (hv : v ∈ V) (dist : u ≠ v)
    (first : outN D V u = insert w C)
    (toBank : C ⊆ outN D V v) (near : w ∈ ball D V v t)
    (path : v ∈ ball D V u k) : v = w := by
  obtain ⟨_, l, fit, road⟩ := mem_ball.mp path
  cases road with
  | refl => exact (dist rfl).elim
  | @step x a z m av xa tail =>
    have ha : a ∈ outN D V u := mem_outN.mpr ⟨av, xa⟩
    rcases mem_insert.mp (first ▸ ha) with same | common
    · subst a
      obtain ⟨_, j, jt, back⟩ := mem_ball.mp near
      by_cases pos : 0 < j
      · exact (free _ _ (by omega) (by omega) (back.append tail)).elim
      · have eq : j = 0 := by omega
        subst j
        cases back
        rfl
    · have va := (mem_outN.mp (toBank common)).2
      exact (free _ _ (by omega) (by omega) (.step av va tail)).elim

/-- Every fast representative misses every other representative with the
same first-layer cycle, even when the other representative is slow. -/
theorem fast_first_side {D V q k u v w C} (free : QFree D V q)
    (time : k+1 ≤ q) (hq : 2 ≤ q) (hv : v ∈ V) (dist : u ≠ v)
    (first : outN D V u = insert w C) (toBank : C ⊆ outN D V v)
    (fast : ∃ x ∈ C, D x w = true) : v ∉ ball D V u k := by
  obtain ⟨x, hx, xw⟩ := fast
  have va := toBank hx
  have wv : w ∈ V := outN_subset (first.symm ▸ mem_insert_self w C)
  have reach := ball_step (X_B1 va) wv xw
  intro hit
  have eq := first_side_contact free (t := 2) (by omega) (by decide) hv dist first toBank reach hit
  subst w
  exact digonfree free hq hv (outN_subset va) (mem_outN.mp va).2 xw

#print axioms second_side_pairs
#print axioms first_side_contact
#print axioms fast_first_side
end LeanCH.BR.PhysicalCycleStock
