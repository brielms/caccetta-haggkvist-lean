import checkpoints.shen_extension.ReturnSignature
import checkpoints.shen_extension.WitnessTargetChoice

namespace LeanCH.BR.ReturnSignature
open Finset BRq2 BRq3 BR45 TripleBank ThirtySixClose

/-- Charge the old backward arc, when present, and every tight middle to y.
The only row which can end below the quota is y itself. -/
theorem spend_at_head {H : CH.Digraph} {U : Finset ℕ} {w y t : ℕ}
    (safe : QFree H U 3) (wu : w∈U) (yu : y∈U) (wy : w≠y) (off : H w y≠true)
    (need : t≤(outN H U w).card+1) (floor : ∀ i∈U, i≠w → t≤(outN H U i).card) :
    ∃ E : CH.Digraph, QFree E U 3 ∧ E w y=true ∧
      (outN E U y).card+(tight H U y w t).card+(H y w).toNat=(outN H U y).card ∧
      ∀ i∈U, i≠y → t≤(outN E U i).card := by
  classical
  let F : CH.Digraph := fun a b => decide (H a b=true ∧ ¬(a=y ∧ b=w))
  have old {a b} (e : F a b=true) : H a b=true := (of_decide_eq_true e).1
  have clean : QFree F U 3 := SignatureRestoration.free_sub safe (fun _ _ h => old h)
  have unchanged {a} (ay : a≠y) : outN F U a=outN H U a := by
    ext b
    simp [mem_outN,F,ay]
  have trimmed : outN F U y=(outN H U y).erase w := by
    ext b
    simp only [mem_outN,F,decide_eq_true_eq,mem_erase,true_and]
    tauto
  let Z := outN H U y ∩ inN H U w
  let K := tight H U y w t
  have nw : w∉Z := fun e => loopfree safe (by decide) wu (mem_inN.mp (mem_inter.mp e).2).2
  have ny : y∉Z := fun e => loopfree safe (by decide) yu (mem_outN.mp (mem_inter.mp e).1).2
  let A (a : ℕ) : Finset ℕ := if a=w then {y} else ∅
  let C (a : ℕ) : Finset ℕ := if a=y then K else if a∈Z ∧ a∉K then {w} else ∅
  have spec {a b} (m : b∈A a) : a=w ∧ b=y := by
    by_cases aw : a=w
    · exact ⟨aw,by simpa [A,aw] using m⟩
    · simp [A,aw] at m
  obtain ⟨ok,rows⟩ := patch_certificate (A:=A) (C:=C) clean
    (fun a _ b m => by
      obtain ⟨rfl,rfl⟩ := spec m
      exact ⟨yu,wy.symm,fun e => off (old e),by simp [F]⟩)
    (fun a _ b m z zu bz za => by
      obtain ⟨rfl,rfl⟩ := spec m
      have zz : z∈Z := mem_inter.mpr ⟨mem_outN.mpr ⟨zu,old bz⟩,mem_inN.mpr ⟨zu,old za⟩⟩
      by_cases k : z∈K
      · exact Or.inl (by simpa [C] using k)
      · exact Or.inr (by simp [C,show z≠b from fun e => ny (e ▸ zz),zz,k]))
    (fun _ _ _ m _ p => by
      obtain ⟨rfl,rfl⟩ := spec m
      exact (wy (spec p).1.symm).elim)
  refine ⟨_,ok,decide_eq_true (Or.inl (by simp [A])),?_,?_⟩
  · have sub : K⊆outN F U y := by
      intro z zm
      have zz := (mem_filter.mp zm).1
      rw [trimmed]
      exact mem_erase.mpr ⟨fun e => nw (e ▸ zz), (mem_inter.mp zz).1⟩
    have dep : (outN F U y).card+(H y w).toNat=(outN H U y).card := by
      rw [trimmed]
      cases e : H y w with
      | false => simp [erase_eq_of_notMem (show w∉outN H U y by simp [mem_outN,e])]
      | true => simpa using card_erase_add_one (mem_outN.mpr ⟨wu,e⟩)
    rw [rows y yu]
    change _ + K.card + _ = _
    simp only [A,C,ite_eq_left rfl,ite_eq_right wy.symm,card_empty,Nat.add_zero]
    have cuts := card_sdiff_of_subset sub
    have fits := card_le_card sub
    omega
  · intro i iu iy
    rw [rows i iu,unchanged iy]
    by_cases iw : i=w
    · subst i
      simpa [A,C,wy,nw] using need
    have fr := floor i iu iw
    by_cases cut : i∈Z ∧ i∉K
    · have hi : t<(outN H U i).card := by
        by_contra! lo
        exact cut.2 (mem_filter.mpr ⟨cut.1,lo⟩)
      have used := card_sdiff_add_card_inter (outN H U i) ({w} : Finset ℕ)
      have cap := (card_le_card (inter_subset_right :
        outN H U i ∩ ({w} : Finset ℕ) ⊆ {w})).trans_eq (card_singleton w)
      simp [A,C,iy,iw,cut]
      omega
    · simpa [A,C,iy,iw,cut] using fr

/-- Source and target may be adjacent in the backward direction. Each small
signature class costs at most one, and reversing that backward arc costs one.
All the outstanding cost can be assigned to the selected head y. -/
theorem grouped_head_charge {H : CH.Digraph} {U : Finset ℕ} {w y t : ℕ}
    (safe : QFree H U 3) (wu : w∈U) (yu : y∈U) (wy : w≠y) (off : H w y≠true)
    (need : t≤(outN H U w).card+1) (floor : ∀ i∈U, i≠w → t≤(outN H U i).card) :
    let K := tight H U y w t
    ∃ E : CH.Digraph, QFree E U 3 ∧ E w y=true ∧
      (outN H U y).card≤(outN E U y).card+smallClasses K (seen H U K 2)+(H y w).toNat ∧
      ∀ i∈U, i≠y → t≤(outN E U i).card := by
  classical
  intro K
  have kv : K⊆U := fun _ h => outN_subset (mem_inter.mp (mem_filter.mp h).1).1
  obtain ⟨J,clean,internal,bound,_⟩ := plan kv (seen H U K 2)
  obtain ⟨G,ok,missing,back,dy,dw,mono,sub⟩ := prepare safe wu yu off floor clean internal
  have b : G y w=H y w := Bool.eq_iff_iff.mpr back
  obtain ⟨E,done,arc,degree,rows⟩ := spend_at_head ok wu yu wy missing (dw ▸ need)
    (fun i iu ne => (floor i iu ne).trans (mono i iu))
  have cap := (card_le_card sub).trans bound
  rw [b,dy] at degree
  exact ⟨E,done,arc,by omega,rows⟩

theorem grouped_head_pays {H : CH.Digraph} {U : Finset ℕ} {w y t : ℕ}
    (safe : QFree H U 3) (wu : w∈U) (yu : y∈U) (wy : w≠y) (off : H w y≠true)
    (need : t≤(outN H U w).card+1) (floor : ∀ i∈U, i≠w → t≤(outN H U i).card)
    (budget : let K := tight H U y w t
      t+smallClasses K (seen H U K 2)+(H y w).toNat≤(outN H U y).card) :
    ∃ E : CH.Digraph, QFree E U 3 ∧ E w y=true ∧ ∀ i∈U, t≤(outN E U i).card := by
  obtain ⟨E,ok,arc,cost,rows⟩ := grouped_head_charge safe wu yu wy off need floor
  dsimp only at budget
  refine ⟨E,ok,arc,fun i iu => ?_⟩
  by_cases iy : i=y
  · subst i; omega
  · exact rows i iu iy

/-- At the one-unit boundary the new sole possible shortage has a specified
physical label: it is the head just installed, including for a reversed arc. -/
theorem grouped_head_shift {H : CH.Digraph} {U : Finset ℕ} {w y t : ℕ}
    (safe : QFree H U 3) (wu : w∈U) (yu : y∈U) (wy : w≠y) (off : H w y≠true)
    (need : t≤(outN H U w).card+1) (floor : ∀ i∈U, i≠w → t≤(outN H U i).card)
    (budget : let K := tight H U y w t
      t+smallClasses K (seen H U K 2)+(H y w).toNat≤(outN H U y).card+1) :
    ∃ E : CH.Digraph, QFree E U 3 ∧ E w y=true ∧
      t≤(outN E U y).card+1 ∧ ∀ i∈U, i≠y → t≤(outN E U i).card := by
  obtain ⟨E,ok,arc,cost,rows⟩ := grouped_head_charge safe wu yu wy off need floor
  dsimp only at budget
  exact ⟨E,ok,arc,by omega,rows⟩

theorem grouped_head_obstruction {H : CH.Digraph} {U : Finset ℕ} {w y t : ℕ}
    (safe : QFree H U 3) (wu : w∈U) (yu : y∈U) (wy : w≠y) (off : H w y≠true)
    (need : t≤(outN H U w).card+1) (floor : ∀ i∈U, i≠w → t≤(outN H U i).card)
    (no : BypassRepair.NoHost 3 t) (size : U.card≤3*t) :
    let K := tight H U y w t
    (outN H U y).card<t+smallClasses K (seen H U K 2)+(H y w).toNat := by
  obtain ⟨E,ok,arc,cost,rows⟩ := grouped_head_charge safe wu yu wy off need floor
  intro K
  by_contra! affordable
  have yf : t≤(outN E U y).card := by dsimp only [K] at affordable; omega
  exact no E U ⟨w,wu⟩ size ok (fun i iu => by
    by_cases same : i=y
    · simpa [same] using yf
    · exact rows i iu same)

/-- For a nonadjacent target, one extra unit can instead be routed to a
tight middle in an original class of size at most three. -/
theorem grouped_middle_shift {H : CH.Digraph} {U : Finset ℕ} {w y t : ℕ}
    (safe : QFree H U 3) (wu : w∈U) (yu : y∈U) (wy : w≠y)
    (off : H w y≠true) (back : H y w≠true)
    (need : t≤(outN H U w).card+1) (floor : ∀ i∈U, i≠w → t≤(outN H U i).card)
    (budget : let K := tight H U y w t
      t+smallClasses K (seen H U K 2)≤(outN H U y).card+1) :
    let K := tight H U y w t
    (∃ E : CH.Digraph, QFree E U 3 ∧ E w y=true ∧ ∀ i∈U,t≤(outN E U i).card) ∨
      ∃ z∈K, (K.filter (fun b => seen H U K 2 b=seen H U K 2 z)).card≤3 ∧
        ∃ E : CH.Digraph, QFree E U 3 ∧ E w y=true ∧ E z w≠true ∧
          t≤(outN E U z).card+1 ∧ ∀ i∈U, i≠z → t≤(outN E U i).card := by
  classical
  intro K
  change t+smallClasses K (seen H U K 2)≤_ at budget
  have kv : K⊆U := fun _ h => outN_subset (mem_inter.mp (mem_filter.mp h).1).1
  obtain ⟨J,clean,internal,bound,small⟩ := plan kv (seen H U K 2)
  obtain ⟨G,ok,missing,backward,dy,dw,mono,sub⟩ := prepare safe wu yu off floor clean internal
  have noBack := fun h => back (backward.mp h)
  have gf : ∀ i∈U,i≠w → t≤(outN G U i).card := fun i iu ne => (floor i iu ne).trans (mono i iu)
  let T := tight G U y w t
  have cap : T.card≤smallClasses K (seen H U K 2) := (card_le_card sub).trans bound
  by_cases enough : t+T.card≤(outN G U y).card
  · exact Or.inl (one_arc_return_budget ok wu yu wy missing noBack (dw ▸ need) gf enough)
  have yf := gf y yu wy.symm
  have pos : 0<T.card := by omega
  obtain ⟨z,zt⟩ := card_pos.mp pos
  obtain ⟨zk,sink⟩ := mem_filter.mp (sub zt)
  have allowance : t+T.card≤(outN G U y).card+1 := by omega
  obtain ⟨E,good,arc,cut,_,short,rows⟩ :=
    WalkReturn.deficit_shift ok wu yu wy missing noBack (dw ▸ need) gf zt allowance
  exact Or.inr ⟨z,zk,small z zk sink,E,good,arc,cut,short,rows⟩

#print axioms grouped_middle_shift
/-- Select the destination of the shortage before choosing the residual graph
or the common target. If at most three candidate labels have inherited arcs
into this destination, every tight middle of the selected repair is exterior. -/
theorem external_middle_of_small_pool {D : CH.Digraph} {W : Finset ℕ}
    (native : QFree D W 3) (live : W.Nonempty) (small : W.card≤3) :
    ∃ w∈W, ∀ {H : CH.Digraph} {U : Finset ℕ} {t y : ℕ},
      QFree H U 3 → w∈U → y∈U → w≠y → H w y≠true →
      t≤(outN H U w).card+1 → (∀ i∈U, i≠w → t≤(outN H U i).card) →
      BypassRepair.NoHost 3 t → U.card≤3*t →
      (∀ m∈W, H m w=true → D m w=true) →
      t+(H y w).toNat≤(outN H U y).card →
      ∃ z∈tight H U y w t, z∉W := by
  classical
  obtain ⟨w,wm,source⟩ := exists_sink native.reverse live small
  refine ⟨w,wm,?_⟩
  intro H U t y safe wu yu wy off need floor no size inherit affordable
  have obstruction := grouped_head_obstruction safe wu yu wy off need floor no size
  let K := tight H U y w t
  have occupied : K.Nonempty := by
    by_contra empty
    have e := not_nonempty_iff_eq_empty.mp empty
    change (outN H U y).card < t+smallClasses K (seen H U K 2)+(H y w).toNat at obstruction
    simp [e,smallClasses] at obstruction
    omega
  obtain ⟨z,zk⟩ := occupied
  refine ⟨z,zk,fun zm => ?_⟩
  exact source z zm (inherit z zm (mem_inN.mp (mem_inter.mp (mem_filter.mp zk).1).2).2)

/-- For a target of the deleted bank, count only the shortened return
middles. The formula includes the case where the target points to w. -/
theorem common_target_classes {D H : CH.Digraph} {V B : Finset ℕ} {t w y : ℕ}
    (native : QFree D V 3) (reg : OutEq (t+1) D V) (bv : B⊆V)
    (wu : w∈V\B) (yu : y∈V\B) (common : ∀ b∈B, D b y=true)
    (safe : QFree H (V\B) 3) (wy : w≠y) (off : H w y≠true)
    (need : t≤(outN H (V\B) w).card+1)
    (floor : ∀ i∈V\B, i≠w → t≤(outN H (V\B) i).card)
    (no : BypassRepair.NoHost 3 t) (size : (V\B).card≤3*t)
    (oldY : outN H (V\B) y⊆outN D (V\B) y) :
    let U := V\B
    let R := (outN H U y ∩ inN H U w).filter (fun m => (outN H U m).card<(outN D U m).card)
    (outN H U y).card<t+smallClasses R (seen H U R 2)+(H y w).toNat := by
  classical
  intro U R
  have eq : tight H U y w t=R := by
    ext z
    simp only [tight,R,mem_filter]
    apply and_congr_right
    intro hit
    obtain ⟨zu,yz⟩ := mem_outN.mp (oldY (mem_inter.mp hit).1)
    have miss : outN D B z=∅ := eq_empty_iff_forall_notMem.mpr (fun b bm =>
      native b 3 (by decide) (by decide) (.step (sdiff_subset yu) (common b (outN_subset bm))
        (.step (sdiff_subset zu) yz (.step (bv (outN_subset bm)) (mem_outN.mp bm).2 (.refl _)))))
    have split := card_outN_union (D:=D) (show Disjoint B U from disjoint_sdiff) z
    rw [union_sdiff_of_subset bv,reg z (sdiff_subset zu),miss,card_empty,zero_add] at split
    omega
  have obstruction := grouped_head_obstruction safe wu yu wy off need floor no size
  change _ < t+smallClasses (tight H U y w t) (seen H U (tight H U y w t) 2)+(H y w).toNat at obstruction
  rwa [eq] at obstruction

/-- Apply the actual deficit shift, choosing its unpaid middle at a source
of the original tight pool. For this single residual, every affordable new
head would require a tight return from outside the original pool. -/
theorem shift_forces_external {H : CH.Digraph} {U : Finset ℕ} {x p t : ℕ}
    (safe : QFree H U 3) (xu : x∈U) (pu : p∈U) (xp : x≠p)
    (off : H x p≠true) (back : H p x≠true)
    (need : t≤(outN H U x).card+1) (floor : ∀ i∈U, i≠x → t≤(outN H U i).card)
    (no : BypassRepair.NoHost 3 t) (size : U.card≤3*t)
    (live : (tight H U p x t).Nonempty) (small : (tight H U p x t).card≤3)
    (budget : t+(tight H U p x t).card≤(outN H U p).card+1) :
    let W := tight H U p x t
    ∃ w∈W, ∃ E : CH.Digraph, QFree E U 3 ∧ E x p=true ∧ E w x≠true ∧
      t≤(outN E U w).card+1 ∧ (∀ i∈U, i≠w → t≤(outN E U i).card) ∧
      ∀ y∈U, w≠y → E w y≠true → t+(E y w).toNat≤(outN E U y).card →
        ∃ z∈tight E U y w t, z∉W := by
  classical
  intro W
  have sub : W⊆U := fun _ h => outN_subset (mem_inter.mp (mem_filter.mp h).1).1
  obtain ⟨w,wm,force⟩ := external_middle_of_small_pool (safe.mono_set sub) live small
  obtain ⟨E,ok,arc,cut,old,near,rows⟩ :=
    WalkReturn.deficit_shift safe xu pu xp off back need floor wm budget
  have wp : w≠p := fun e => loopfree safe (by decide) pu
    (e ▸ (mem_outN.mp (mem_inter.mp (mem_filter.mp wm).1).1).2)
  refine ⟨w,wm,E,ok,arc,cut,near,rows,?_⟩
  intro y yu wy missing room
  apply force ok (sub wm) yu wy missing near rows no size _ room
  intro m _ ed
  exact (old m w ed).elim id (fun e => (wp e.2).elim)

#print axioms shift_forces_external

#print axioms grouped_head_pays
#print axioms common_target_classes
#print axioms external_middle_of_small_pool

#print axioms grouped_head_charge
#print axioms grouped_head_shift
#print axioms grouped_head_obstruction
end LeanCH.BR.ReturnSignature
