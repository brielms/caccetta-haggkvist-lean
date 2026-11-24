import checkpoints.shen_extension.ColumnRecurrence

namespace LeanCH.BR.Closure.ColumnBlockerEscape
open Finset BRq2 BRq3 BR45

/-- Arcs join different labels at forward distance at most k. -/
noncomputable def radiusGraph (D : CH.Digraph) (V : Finset ℕ) (k : ℕ) : CH.Digraph := by
  classical exact fun a b => decide (b∈(ball D V a k).erase a)

theorem radius_row {D V k a} : outN (radiusGraph D V k) V a=(ball D V a k).erase a := by
  classical
  ext b
  simp only [mem_outN,radiusGraph,decide_eq_true_eq,and_iff_right_iff_imp]
  exact fun h => ball_subset (mem_of_mem_erase h)

theorem lift_radius {D V k a b j} (path : Walk (radiusGraph D V k) V a b j) :
    ∃ m, j≤m ∧ m≤j*k ∧ Walk D V a b m := by
  induction path with
  | refl => exact ⟨0,by omega,by simp,.refl _⟩
  | @step x y z n yv xy rest ih =>
    have hit : y∈(ball D V x k).erase x := of_decide_eq_true xy
    obtain ⟨ne,reach⟩ := mem_erase.mp hit
    obtain ⟨r,short,w⟩ := (mem_ball.mp reach).2
    have pos : 0<r := by
      by_contra! zero
      have eq : r=0 := by omega
      subst r; cases w; exact ne rfl
    obtain ⟨m,lo,hi,tail⟩ := ih
    refine ⟨r+m,by omega,?_,w.append tail⟩
    rw [Nat.add_mul,one_mul]; omega

theorem radius_safe {D V k q} (safe : QFree D V q) (room : 3*k≤q) :
    QFree (radiusGraph D V k) V 3 := by
  intro a j pos short path
  obtain ⟨m,lo,hi,w⟩ := lift_radius path
  exact safe a m (pos.trans lo) (hi.trans ((Nat.mul_le_mul_right k short).trans room)) w

/-- The triangle-family rule at every admissible Shen radius. A small
ball is an explicit alternative, so no unproved growth bound is assumed. -/
theorem radius_alternative {D V q k t} (safe : QFree D V q) (ne : V.Nonempty)
    (room : 3*k≤q) (budget : V.card≤3*t) :
    (∃ a∈V, (ball D V a k).card≤t) ∨
    let E := radiusGraph D V k
    (∃ u∈V, ∃ v∈V, Unmatched E V u ∧ Unmatched E V v ∧
      (ball D V u k).erase u ≠ (ball D V v k).erase v) ∧
    ∀ X⊆V, (∀a∈X, ∃b∈X, Matches E V a b) →
      (3*t+1-V.card)*X.card ≤ ∑ z∈unmatchedSet E V, (outN E X z).card := by
  classical
  by_cases low : ∃ a∈V, (ball D V a k).card≤t
  · exact Or.inl low
  right
  have deg (a) (av : a∈V) : t≤(outN (radiusGraph D V k) V a).card := by
    rw [radius_row]
    have eq := card_erase_add_one (self_mem_ball (D:=D) (k:=k) av)
    have gt : t<(ball D V a k).card := by by_contra! le; exact low ⟨a,av,le⟩
    omega
  have free := radius_safe safe room
  obtain ⟨u,uv,v,vv,um,vm,diff⟩ := distinct_unmatched free ne deg budget
  exact ⟨⟨u,uv,v,vv,um,vm,by simpa only [radius_row] using diff⟩,
    fun _ sub renew => (recurrence free deg (by have := card_pos.mpr ne; omega) budget sub renew).2⟩

#print axioms radius_safe
#print axioms radius_alternative
end LeanCH.BR.Closure.ColumnBlockerEscape
