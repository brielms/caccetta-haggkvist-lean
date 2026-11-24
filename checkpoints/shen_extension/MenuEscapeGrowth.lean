import checkpoints.shen_extension.SharedExitReturn
import LeanCH.BR.BRq2Ball

namespace LeanCH.BR.SATBoundaryPilot

open Finset BRq2 BRq3

/-- Count the actual target labels reached by a fixed horizon. Every sink in
the reached part of X sends its other heads into the next new layer of X. -/
theorem menu_escape_growth_of_frontier {D : CH.Digraph} {V X T : Finset ℕ} {x q k r : ℕ}
    (free : QFree D V q) (xs : X ⊆ V) (ts : T ⊆ V)
    (size : (X ∩ ball D V x r).card ≤ q) (start : x ∈ X)
    (budget : ∀ z ∈ X, k ≤ (outN D (X ∪ T) z).card) :
    let m := (T ∩ ball D V x (r+1)).card
    1 + ((outN D (X ∪ T) x).card - m) + r * (k-m) ≤
      (X ∩ ball D V x (r+1)).card := by
  classical
  let A (j : ℕ) := X ∩ ball D V x j
  let F := T ∩ ball D V x (r+1)
  let m := F.card
  have root (j : ℕ) : x ∈ A j := mem_inter.mpr ⟨start, self_mem_ball (xs start)⟩
  have mono (j : ℕ) : A j ⊆ A (j+1) :=
    fun _ hy => mem_inter.mpr ⟨(mem_inter.mp hy).1, ball_mono_radius (by omega) (mem_inter.mp hy).2⟩
  have step (j : ℕ) (early : j ≤ r) :
      (A j).card + (k-m) ≤ (A (j+1)).card := by
    have inside : A j ⊆ X := inter_subset_left
    obtain ⟨z,hz,sink⟩ := exists_sink (free.mono_set (inside.trans xs))
      ⟨x,root j⟩ ((card_le_card (show A j ⊆ A r from fun _ hv =>
        mem_inter.mpr ⟨(mem_inter.mp hv).1, ball_mono_radius early (mem_inter.mp hv).2⟩)).trans size)
    have sub : outN D (X ∪ T) z ⊆ (A (j+1) \ A j) ∪ F := by
      intro y hy
      obtain ⟨menu, edge⟩ := mem_outN.mp hy
      have nextBall := ball_step (mem_inter.mp hz).2 ((union_subset xs ts) menu) edge
      rcases mem_union.mp menu with h | h
      · exact mem_union_left _ (mem_sdiff.mpr ⟨mem_inter.mpr ⟨h,nextBall⟩,
          fun old => sink y old edge⟩)
      · exact mem_union_right _ (mem_inter.mpr ⟨h,ball_mono_radius (by omega) nextBall⟩)
    have cap := (card_le_card sub).trans (card_union_le _ _)
    rw [card_sdiff_of_subset (mono j)] at cap
    have := budget z (inside hz)
    have := card_le_card (mono j)
    dsimp [m]
    omega
  have first : 1 + ((outN D (X ∪ T) x).card - m) ≤ (A 1).card := by
    have sub : outN D (X ∪ T) x ⊆ ((A 1).erase x) ∪ F := by
      intro y hy
      obtain ⟨menu,edge⟩ := mem_outN.mp hy
      have path := (mem_ball_one (xs start)).mpr (Or.inr
        (mem_outN.mpr ⟨(union_subset xs ts) menu,edge⟩))
      rcases mem_union.mp menu with h | h
      · have diff : y ≠ x := by
          intro eq
          subst y
          have pos := card_pos.mpr (show (X ∩ ball D V x r).Nonempty from ⟨x,root r⟩)
          exact free x 1 (by decide) (by omega) (.step (xs start) edge (.refl x))
        exact mem_union_left _ (mem_erase.mpr ⟨diff,mem_inter.mpr ⟨h,path⟩⟩)
      · exact mem_union_right _ (mem_inter.mpr ⟨h,ball_mono_radius (by omega) path⟩)
    have cap := (card_le_card sub).trans (card_union_le _ _)
    rw [card_erase_of_mem (root 1)] at cap
    have pos := card_pos.mpr (show (A 1).Nonempty from ⟨x,root 1⟩)
    dsimp [m]
    omega
  have iter (i : ℕ) (hi : i ≤ r) :
      1 + ((outN D (X ∪ T) x).card - m) + i * (k-m) ≤ (A (i+1)).card := by
    induction i with
    | zero => simpa using first
    | succ i ih =>
      have prev := ih (by omega)
      have next := step (i+1) hi
      rw [Nat.succ_mul]
      omega
  exact iter r le_rfl

theorem menu_escape_growth {D : CH.Digraph} {V X T : Finset ℕ} {x q k r : ℕ}
    (free : QFree D V q) (xs : X ⊆ V) (ts : T ⊆ V) (size : X.card ≤ q)
    (start : x ∈ X) (budget : ∀ z ∈ X, k ≤ (outN D (X ∪ T) z).card) :
    let m := (T ∩ ball D V x (r+1)).card
    1 + ((outN D (X ∪ T) x).card - m) + r * (k-m) ≤
      (X ∩ ball D V x (r+1)).card :=
  menu_escape_growth_of_frontier free xs ts ((card_le_card inter_subset_left).trans size)
    start budget

/-- X is unrestricted. Either its reached part already contains q+1 rows,
or each new layer pays the target deficit in full. -/
theorem menu_escape_growth_any_set {D : CH.Digraph} {V X T : Finset ℕ} {x q k r : ℕ}
    (free : QFree D V q) (xs : X ⊆ V) (ts : T ⊆ V)
    (start : x ∈ X) (budget : ∀ z ∈ X, k ≤ (outN D (X ∪ T) z).card) :
    let m := (T ∩ ball D V x (r+1)).card
    min (q+1) (1 + ((outN D (X ∪ T) x).card - m) + r*(k-m)) ≤
      (X ∩ ball D V x (r+1)).card := by
  by_cases small : (X ∩ ball D V x r).card ≤ q
  · exact (min_le_right _ _).trans (menu_escape_growth_of_frontier free xs ts small start budget)
  · have mono : X ∩ ball D V x r ⊆ X ∩ ball D V x (r+1) := fun _ hv =>
      mem_inter.mpr ⟨(mem_inter.mp hv).1, ball_mono_radius (by omega) (mem_inter.mp hv).2⟩
    exact (min_le_left _ _).trans ((show q+1 ≤ _ by omega).trans (card_le_card mono))

#print axioms menu_escape_growth_any_set

/-- An excess of e available root heads saves e steps in reaching k targets. -/
theorem hits_targets_by_radius {D : CH.Digraph} {V X T : Finset ℕ} {x q k r : ℕ}
    (free : QFree D V q) (xs : X ⊆ V) (ts : T ⊆ V) (size : X.card ≤ q)
    (start : x ∈ X) (budget : ∀ z ∈ X, k ≤ (outN D (X ∪ T) z).card)
    (room : X.card + k ≤ (r+1) + (outN D (X ∪ T) x).card) :
    k ≤ (T ∩ ball D V x (r+1)).card := by
  by_contra! miss
  have growth := menu_escape_growth (r:=r) free xs ts size start budget
  dsimp only at growth
  have bound : (X ∩ ball D V x (r+1)).card ≤ X.card := card_le_card inter_subset_left
  have gap : 1 ≤ k - (T ∩ ball D V x (r+1)).card := by omega
  have speed := Nat.mul_le_mul_left r gap
  rw [Nat.mul_one] at speed
  omega

#print axioms menu_escape_growth
#print axioms hits_targets_by_radius

/-- If all exterior targets can return to x within t steps, the reached part
of X must absorb the whole row budget at each layer up to q-t. -/
theorem short_returns_force_growth {D : CH.Digraph} {V X T : Finset ℕ} {x q k r t : ℕ}
    (free : QFree D V q) (xs : X ⊆ V) (ts : T ⊆ V) (size : X.card ≤ q)
    (start : x ∈ X) (outside : x ∉ T) (room : r+1+t ≤ q)
    (budget : ∀ z ∈ X, k ≤ (outN D (X ∪ T) z).card)
    (returns : ∀ y ∈ T, x ∈ ball D V y t) :
    1 + (outN D (X ∪ T) x).card + r*k ≤ (X ∩ ball D V x (r+1)).card := by
  have empty : T ∩ ball D V x (r+1) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    obtain ⟨yt,hf⟩ := mem_inter.mp hy
    obtain ⟨_,i,hi,fw⟩ := mem_ball.mp hf
    obtain ⟨_,j,hj,bw⟩ := mem_ball.mp (returns y yt)
    have pos : 0 < i := by
      cases i with
      | zero => cases fw; exact (outside yt).elim
      | succ => omega
    exact free x (i+j) (by omega) (by omega) (fw.append bw)
  have h := menu_escape_growth (r:=r) free xs ts size start budget
  dsimp only at h
  simpa [empty] using h

/-- The unlimited seed-3 trace, addition 686619, in its canonical graph
interpretation. C(u,4,k) counts the first four labels other than u.
Root 0 points to each of rows 1,2,3, excluding 0 from their outgoing menus. -/
theorem clause_686619 {D : CH.Digraph} {V : Finset ℕ} {q : ℕ}
    (free : QFree D V q) (cutoff : 3 ≤ q) (labels : range 5 ⊆ V)
    (pin : ∀ z ∈ ({1,2,3} : Finset ℕ), D 0 z = true)
    (budget : ∀ z ∈ ({1,2,3} : Finset ℕ), 1 ≤ (outN D ((range 5).erase z) z).card)
    (extra : 2 ≤ (outN D ((range 5).erase 1) 1).card) :
    4 ∈ ball D V 1 2 := by
  let X : Finset ℕ := {1,2,3}
  let T : Finset ℕ := {4}
  have xs : X ⊆ V := (show X ⊆ range 5 by decide).trans labels
  have ts : T ⊆ V := (show T ⊆ range 5 by decide).trans labels
  have cap (z) (hz : z ∈ X) :
      (outN D ((range 5).erase z) z).card ≤ (outN D (X ∪ T) z).card := by
    apply card_le_card
    intro y hy
    obtain ⟨menu,arc⟩ := mem_outN.mp hy
    have nz : y ≠ 0 := by
      rintro rfl
      exact free 0 2 (by decide) (by omega) (.step (xs hz) (pin z hz)
        (.step (labels (by decide : 0 ∈ range 5)) arc (.refl 0)))
    apply mem_outN.mpr
    rw [show X ∪ T = (range 5).erase 0 by decide]
    exact ⟨mem_erase.mpr ⟨nz,mem_of_mem_erase menu⟩,arc⟩
  have sx : X.card = 3 := by decide
  have one : 1 ∈ X := by decide
  have h1 := extra.trans (cap 1 one)
  have hit := hits_targets_by_radius (r:=1) (k:=1) free xs ts (by omega) one
    (fun z hz => (budget z hz).trans (cap z hz)) (by omega)
  obtain ⟨y,hy⟩ := card_pos.mp hit
  obtain ⟨yt,reach⟩ := mem_inter.mp hy
  have eq : y=4 := mem_singleton.mp yt
  exact eq ▸ reach

#print axioms short_returns_force_growth
#print axioms clause_686619

end LeanCH.BR.SATBoundaryPilot
