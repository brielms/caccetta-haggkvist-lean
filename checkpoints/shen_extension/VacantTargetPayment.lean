import checkpoints.shen_extension.CloneTargetPayment

namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45

/-- Set the incoming and outgoing rows at the previously vacant label. -/
def replaceVacancy (D : CH.Digraph) (c : ℕ) (T O : Finset ℕ) : CH.Digraph :=
  fun v w => if v=c then decide (w∈O) else if w=c then decide (v∈T) else D v w

/-- Credit each row in T once using a new vertex with any independent
outgoing set O of enough heads. -/
theorem vacant_credit {D : CH.Digraph} {J T O : Finset ℕ} {c t : ℕ}
    (safe : QFree D J 3) (fresh : c ∉ J) (small : J.card+1 ≤ 3*t)
    (none : BypassRepair.NoHost 3 t)
    (inside : O ⊆ J) (outside : Disjoint O T) (size : t ≤ O.card)
    (clear : ∀ v ∈ O, ∀ w ∈ T, w ∈ J → D v w ≠ true)
    (paid : ∀ v ∈ J, t ≤ (outN D J v).card + (if v∈T then 1 else 0)) : False := by
  classical
  let E := replaceVacancy D c T O
  let U := insert c J
  have neq {v} (vj : v ∈ J) : v ≠ c := fun e => fresh (e ▸ vj)
  have old {v w} (vj : v ∈ J) (wj : w ∈ J) : E v w = true ↔ D v w = true := by
    simp [E,replaceVacancy,neq vj,neq wj]
  have inc {v} (vj : v ∈ J) : E v c = true ↔ v ∈ T := by
    simp [E,replaceVacancy,neq vj]
  have out {w} : E c w = true ↔ w ∈ O := by simp [E,replaceVacancy]
  have noLoop : E c c ≠ true := fun e => fresh (inside (out.mp e))
  have ok : QFree E U 3 := by
    apply DotOriginalStarReturn.qfree_three_of_tests
    · intro a au ea
      rcases mem_insert.mp au with rfl | aj
      · exact noLoop ea
      · exact loopfree safe (by decide) aj ((old aj aj).mp ea)
    · intro a au b bu e f
      rcases mem_insert.mp au with rfl | aj
      · have bo := out.mp e
        exact disjoint_left.mp outside bo ((inc (inside bo)).mp f)
      rcases mem_insert.mp bu with rfl | bj
      · exact disjoint_left.mp outside (out.mp f) ((inc aj).mp e)
      · exact digonfree safe (by decide) aj bj ((old aj bj).mp e) ((old bj aj).mp f)
    · intro a au b bu d du ab bd da
      have back {v w} (cv : E c v = true) (vw : E v w = true) (wc : E w c = true)
          (wj : w ∈ U) : False := by
        have vo := out.mp cv
        rcases mem_insert.mp wj with rfl | wj
        · exact noLoop wc
        · exact clear v vo w ((inc wj).mp wc) wj ((old (inside vo) wj).mp vw)
      rcases mem_insert.mp au with rfl | aj
      · exact back ab bd da du
      rcases mem_insert.mp bu with rfl | bj
      · exact back bd da ab au
      rcases mem_insert.mp du with rfl | dj
      · exact back da ab bd bu
      · exact safe a 3 (by decide) (by decide)
          (.step bj ((old aj bj).mp ab) (.step dj ((old bj dj).mp bd)
            (.step aj ((old dj aj).mp da) (.refl _))))
  have uv : U.card ≤ 3*t := by simpa [U,card_insert_of_notMem fresh] using small
  apply none E U (show U.Nonempty from ⟨c,mem_insert_self ..⟩) uv ok
  intro v vu
  rcases mem_insert.mp vu with vEq | vj
  · subst v
    have eq : outN E U c = O := by
      ext w
      exact ⟨fun h => out.mp (mem_outN.mp h).2,
        fun h => mem_outN.mpr ⟨mem_insert_of_mem (inside h),out.mpr h⟩⟩
    rwa [eq]
  · have eq : outN E U v = outN D J v ∪ (if v∈T then {c} else ∅) := by
      ext w
      by_cases wc : w=c
      · subst w
        by_cases vt : v ∈ T <;> simp [mem_outN, U, fresh, inc vj, vt]
      · by_cases wj : w∈J
        · by_cases vt : v ∈ T <;> simp [mem_outN,U,wc,wj,old vj wj,vt]
        · by_cases vt : v ∈ T <;> simp [mem_outN,U,wc,wj,vt]
    rw [eq]
    by_cases vt : v∈T
    · rw [ite_eq_left vt,union_singleton,card_insert_of_notMem (fun h => fresh (outN_subset h))]
      simpa [vt] using paid v vj
    · simpa [vt] using paid v vj

/-- Law R′ on the vacant carrier. All successors for the replacement vertex
may be chosen from the original vertices outside T that have no head in T. -/
theorem vacant_payment_bound {D : CH.Digraph} {J L T : Finset ℕ} {c a b p q t : ℕ}
    (safe : QFree D J 3) (fresh : c ∉ J) (small : J.card+1 ≤ 3*t)
    (none : BypassRepair.NoHost 3 t)
    (sub : L ⊆ J) (pl : p ∈ L) (ql : q ∈ L) (pq : p ≠ q)
    (au : a ∈ J) (bu : b ∈ J) (ab : a ≠ b) (al : a ∉ L) (bl : b ∉ L)
    (neutral : ∀ l ∈ L, D l a ≠ true ∧ D l b ≠ true)
    (ap : D a p ≠ true) (bq : D b q ≠ true)
    (parents : ∀ v ∈ ({a,b} : Finset ℕ), t ≤ (outN D J v).card+1 + (if v∈T then 1 else 0))
    (floor : ∀ v ∈ J, v ≠ a → v ≠ b → t ≤ (outN D J v).card + (if v∈T then 1 else 0))
    (fullP : t+1 ≤ (outN D J p).card) (fullQ : t+1 ≤ (outN D J q).card)
    (spare : ∀ w ∈ (outN D J p \ L) ∪ (outN D J q \ L), t+1 ≤ (outN D J w).card)
    (budget : (((outN D J p \ L) ∩ (outN D J q \ L)) \ T).card ≤
      (1 + (if p∈T then 1 else 0)) + (1 + (if q∈T then 1 else 0)))
    (backA : a ∈ T ∨ ∃ d ∈ T ∩ J, D a d = true)
    (backB : b ∈ T ∨ ∃ d ∈ T ∩ J, D b d = true) :
    ((J \ T).filter (fun v => Disjoint (outN D J v) T)).card < t := by
  classical
  by_contra! enough
  let O := (J \ T).filter (fun v => Disjoint (outN D J v) T)
  obtain ⟨E,ok,paid,edges,_⟩ := pair_payment_patch safe sub pl ql pq au bu ab al bl neutral ap bq
    parents floor fullP fullQ spare budget
  have oj : O ⊆ J := (filter_subset ..).trans sdiff_subset
  have ot : Disjoint O T := (disjoint_sdiff : Disjoint T (J \ T)).symm.mono_left (filter_subset ..)
  have noTail {v} (h : v ∈ T ∨ ∃ d ∈ T ∩ J, D v d = true) : v ∉ O := by
    intro vo
    rcases h with vt | h
    · exact disjoint_left.mp ot vo vt
    obtain ⟨d,ds,vd⟩ := h
    exact disjoint_left.mp (mem_filter.mp vo).2
      (mem_outN.mpr ⟨(mem_inter.mp ds).2,vd⟩) (mem_inter.mp ds).1
  refine vacant_credit ok fresh small none oj ot enough ?_ paid
  intro v vo w wt wj e
  rcases edges v w e with old | new | new
  · exact disjoint_left.mp (mem_filter.mp vo).2 (mem_outN.mpr ⟨wj,old⟩) wt
  · exact noTail backA (new.1 ▸ vo)
  · exact noTail backB (new.1 ▸ vo)

#print axioms vacant_credit
#print axioms vacant_payment_bound
end LeanCH.BR.TripleBank
