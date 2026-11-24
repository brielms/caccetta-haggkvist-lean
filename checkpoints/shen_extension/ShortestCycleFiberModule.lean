import checkpoints.shen_extension.AnchoredShiftFlow

namespace LeanCH.BR.Closure.ShortestCycleFiberModule
open Finset BRq2 BRq3 BR45 BRsub ShenCycleSuccessor

/-- Every label that fits in this two-edge slot gives another shortest cycle
with exactly the same fixed path. -/
theorem slots {D W q M S a u b} (hq : 1≤q) (safe : QFree D W q)
    (c : Cycle D W q M) (am : a∈M) (um : u∈M) (bm : b∈M)
    (sv : S⊆W) (us : u∈S) (arcs : ∀x∈S,D a x=true ∧ D x b=true) :
    Disjoint (M.erase u) S ∧ ∀x∈S,Cycle D W q (insert x (M.erase u)) := by
  classical
  have au := (arcs u us).1
  have ub := (arcs u us).2
  have an : a≠u := fun eq => loopfree safe hq (c.sub um) (eq ▸ au)
  have bn : b≠u := fun eq => loopfree safe hq (c.sub um) (eq ▸ ub)
  let P := M.erase u
  have ap : a∈P := mem_erase.mpr ⟨an,am⟩
  have bp : b∈P := mem_erase.mpr ⟨bn,bm⟩
  have away (x) (xs : x∈S) : x∉P := by
    intro xp
    have eq := card_le_one.mp (c.heads a am).le x
      (mem_outN.mpr ⟨mem_of_mem_erase xp,(arcs x xs).1⟩) u (mem_outN.mpr ⟨um,au⟩)
    exact (mem_erase.mp xp).1 eq
  have fits (x) (xs : x∈S) : Cycle D W q (insert x P) := by
    have sub := insert_subset (sv xs) (erase_subset u M |>.trans c.sub)
    have size : (insert x P).card=q+1 := by
      rw [card_insert_of_notMem (away x xs)]
      change (M.erase u).card+1=q+1
      rw [card_erase_add_one um,c.size]
    have deg (i) (hin : i∈insert x P) : 1≤(outN D (insert x P) i).card := by
      rcases mem_insert.mp hin with rfl | ip
      · exact card_pos.mpr ⟨b,mem_outN.mpr ⟨mem_insert_of_mem bp,(arcs i xs).2⟩⟩
      obtain ⟨j,hj⟩ := card_pos.mp (by rw [c.heads i (mem_of_mem_erase ip)]; decide : 0<(outN D M i).card)
      obtain ⟨jm,ij⟩ := mem_outN.mp hj
      by_cases eq : j=u
      · subst j
        have ia := card_le_one.mp (c.incoming u um).le i (mem_inN.mpr ⟨mem_of_mem_erase ip,ij⟩) a
          (mem_inN.mpr ⟨am,au⟩)
        exact card_pos.mpr ⟨x,mem_outN.mpr ⟨mem_insert_self _ _,ia ▸ (arcs x xs).1⟩⟩
      · exact card_pos.mpr ⟨j,mem_outN.mpr ⟨mem_insert_of_mem (mem_erase.mpr ⟨eq,jm⟩),ij⟩⟩
    have r := dt_reg hq (ball_q_one q hq) (safe.mono_set sub) deg (by simpa using size)
    exact ⟨sub,size,r.1,r.2⟩
  exact ⟨disjoint_left.mpr (fun _ xp xs => away _ xs xp),fits⟩

/-- If a→u→b lies on a shortest cycle and every x in S fits in the same
slot a→x→b, then the fixed path cannot distinguish any two members of S.
In a prime source a distinguishing vertex must lie beyond both sets. -/
theorem exterior_splitter {D V W q M S a u b} (hq : 1≤q)
    (safe : QFree D W q) (prime : ShenPrimeTransition.Prime D V) (wv : W⊆V)
    (c : Cycle D W q M) (am : a∈M) (um : u∈M) (bm : b∈M)
    (sv : S⊆W) (many : 2≤S.card) (us : u∈S)
    (arcs : ∀x∈S,D a x=true ∧ D x b=true) :
    ∃z∈V\(M∪S),∃x∈S,∃y∈S,D x z≠D y z ∨ D z x≠D z y := by
  classical
  let P := M.erase u
  have ⟨dis,fits⟩ := slots hq safe c am um bm sv us arcs
  have away (x) (xs : x∈S) : x∉P := fun xp => disjoint_left.mp dis xp xs
  have an : a≠u := fun eq => loopfree safe hq (c.sub um) (eq ▸ (arcs u us).1)
  have bn : b≠u := fun eq => loopfree safe hq (c.sub um) (eq ▸ (arcs u us).2)
  have ap : a∈P := mem_erase.mpr ⟨an,am⟩
  have bp : b∈P := mem_erase.mpr ⟨bn,bm⟩
  have pattern (x) (xs : x∈S) (z) (zp : z∈P) :
      (D x z=true ↔ z=b) ∧ (D z x=true ↔ z=a) := by
    have cs := fits x xs
    have xn := mem_insert_self x P
    exact ⟨⟨fun xz => card_le_one.mp (cs.heads x xn).le z (mem_outN.mpr ⟨mem_insert_of_mem zp,xz⟩)
      b (mem_outN.mpr ⟨mem_insert_of_mem bp,(arcs x xs).2⟩),fun eq => eq ▸ (arcs x xs).2⟩,
      ⟨fun zx => card_le_one.mp (cs.incoming x xn).le z (mem_inN.mpr ⟨mem_insert_of_mem zp,zx⟩)
      a (mem_inN.mpr ⟨mem_insert_of_mem ap,(arcs x xs).1⟩),fun eq => eq ▸ (arcs x xs).1⟩⟩
  have proper : S≠V := fun eq => away a (eq.symm ▸ wv (c.sub am)) ap
  have broken := prime S (sv.trans wv) many proper
  unfold OutUniform InUniform at broken
  by_contra! miss
  have both (x) (xs : x∈S) (y) (ys : y∈S) (z) (zv : z∈V) (zs : z∉S) :
      D x z=D y z ∧ D z x=D z y := by
    by_cases zm : z∈M
    · have zp : z∈P := mem_erase.mpr ⟨fun eq => zs (eq ▸ us),zm⟩
      obtain ⟨f,g⟩ := pattern x xs z zp
      obtain ⟨j,k⟩ := pattern y ys z zp
      exact ⟨Bool.eq_iff_iff.mpr (f.trans j.symm),Bool.eq_iff_iff.mpr (g.trans k.symm)⟩
    · exact miss z (mem_sdiff.mpr ⟨zv,fun t => (mem_union.mp t).elim zm zs⟩) x xs y ys
  exact broken ⟨fun x xs y ys z zv zs => (both x xs y ys z zv zs).1,
    fun x xs y ys z zv zs => (both x xs y ys z zv zs).2⟩

#print axioms exterior_splitter
end LeanCH.BR.Closure.ShortestCycleFiberModule
