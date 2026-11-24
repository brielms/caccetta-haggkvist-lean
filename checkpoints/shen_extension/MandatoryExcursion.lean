import checkpoints.shen_extension.MandatoryTwoStep

namespace LeanCH.BR.Closure.MandatoryExcursion
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor MandatoryTwoStep PuncturedDistance

/-- The forward distance on a reference shortest cycle. Going from a vertex
back to itself takes one full turn. -/
noncomputable def span (D : CH.Digraph) (V : Finset ℕ) (q i j : ℕ) : ℕ :=
  if i = j then q+1 else depth D V i j

private theorem destinations {D W a b n} (w : Walk D W a b n) :
    ∃ U ⊆ W, U.card ≤ n ∧ Walk D U a b n := by
  induction w with
  | refl => exact ⟨∅,empty_subset _,by simp,.refl _⟩
  | @step a b c k bw ab tail ih =>
    obtain ⟨U,sub,small,inner⟩ := ih
    exact ⟨insert b U,insert_subset bw sub,(card_insert_le _ _).trans (by omega),
      .step (mem_insert_self _ _) ab (inner.mono (subset_insert _ _))⟩

/-- A boundary-length closed walk supplies a shortest cycle at its own base. -/
theorem closed_cycle_through {D W q i} (hq : 1 ≤ q) (free : QFree D W q)
    (w : Walk D W i i (q+1)) : ∃ C, Cycle D W q C ∧ i ∈ C := by
  obtain ⟨U,uw,small,loop⟩ := destinations w
  obtain ⟨_,_,iu,_⟩ := loop.unsnoc
  obtain ⟨C,cu,size,deg⟩ := boundary_closed_walk_support (free.mono_set uw) loop
  obtain rfl : C=U := eq_of_subset_of_card_le cu (size ▸ small)
  have reg := dt_reg hq (ball_q_one q hq) (free.mono_set uw) deg (by simpa using size)
  exact ⟨_,⟨uw,size,reg.1,reg.2⟩,iu⟩

/-- A replacement that misses a mandatory vertex, closed up by the old return
segment which also misses it, must strictly exceed the old forward length. -/
theorem strict_detour {D V q i j z d b l} (hq : 1 ≤ q) (free : QFree D V q)
    (mandatory : Forces D V q i z) (total : d+b=q+1) (positive : 0<l)
    (excursion : Walk D (V.erase z) i j l) (back : Walk D (V.erase z) j i b) : d < l := by
  by_contra! cheaper
  have w := excursion.append back
  have upper : l+b ≤ q+1 := by omega
  by_cases short : l+b ≤ q
  · exact free i (l+b) (by omega) short (w.mono (erase_subset _ _))
  · have len : l+b=q+1 := by omega
    rw [len] at w
    obtain ⟨C,c,ic⟩ := closed_cycle_through hq (free.mono_set (erase_subset z V)) w
    exact (forces_iff.mp mandatory) ⟨C,c,ic⟩

private theorem obtain_depth {D V i j} (reach : ∃ k, Walk D V i j k) :
    Walk D V i j (depth D V i j) := by
  classical
  simpa only [depth,dite_eq_left reach] using Nat.find_spec reach

/-- The two segments on the named reference cycle, including the full-turn
convention. The first has length measured in the full graph. -/
theorem segments {D V C q i j} (hq : 1≤q) (free : QFree D V q) (c : Cycle D V q C)
    (ic : i∈C) (jc : j∈C) :
    let d := span D V q i j
    1≤d ∧ d≤q+1 ∧ Walk D C i j d ∧ Walk D C j i (q+1-d) := by
  have heads (x) (xc : x∈C) : ∃y∈C, D x y=true := by
    obtain ⟨y,hy⟩ := card_pos.mp (show 0<(outN D C x).card by rw [c.heads x xc]; decide)
    exact ⟨y,mem_outN.mp hy⟩
  have split {x y} (xc : x∈C) (yc : y∈C) (ne : x≠y) :=
    WeightedSD.tight_cycle_complementary_walks (free.mono_set c.sub) c.size heads xc yc ne
  by_cases eq : i=j
  · subst j
    obtain ⟨y,yc,iy⟩ := heads i ic
    have ne : i≠y := by rintro rfl; exact loopfree free hq (c.sub ic) iy
    obtain ⟨u,_,bound,front,back⟩ := split ic yc ne
    have loop : Walk D C i i (q+1) := by
      simpa only [show u+(q+1-u)=q+1 by omega] using front.append back
    have self : span D V q i i = q+1 := by simp [span]
    simpa only [self,Nat.sub_self] using
      (show 1≤q+1 ∧ q+1≤q+1 ∧ Walk D C i i (q+1) ∧ Walk D C i i 0 from
        ⟨by omega,le_rfl,loop,.refl _⟩)
  · obtain ⟨u,positive,bound,front,back⟩ := split ic jc eq
    have short := depth_le_walk (front.mono c.sub)
    have real : depth D V i j = u := by
      apply le_antisymm short
      by_contra! less
      have alt := obtain_depth (show ∃ k,Walk D V i j k from ⟨u,front.mono c.sub⟩)
      exact free i (depth D V i j+(q+1-u)) (by omega) (by omega) (alt.append (back.mono c.sub))
    simpa only [span,ite_eq_right eq,real] using
      (show 1≤u ∧ u≤q+1 ∧ Walk D C i j u ∧ Walk D C j i (q+1-u) from
        ⟨positive,by omega,front,back⟩)

/-- A mandatory label strictly inside the reference arc forces every exterior
excursion to lose at least one step against the reference arc. -/
theorem excursion_bound {D V C K q i j z y p k} (hq : 1≤q) (free : QFree D V q)
    (c : Cycle D V q C) (ic : i∈C) (jc : j∈C) (zk : z∈K)
    (mandatory : Forces D V q i z) (positive : 0<depth D V i z)
    (between : depth D V i z < span D V q i j)
    (yu : y∈V\K) (iy : D i y=true) (pj : D p j=true) (path : Walk D (V\K) y p k) :
    1 ≤ span D V q i j ∧ span D V q i j ≤ k+1 ∧ Walk D C i j (span D V q i j) := by
  obtain ⟨pos,bound,front,back⟩ := segments hq free c ic jc
  have iz : i≠z := by
    rintro rfl
    have zero := depth_le_walk (Walk.refl (D:=D) (W:=V) i)
    omega
  have jz : j≠z := by
    rintro rfl
    by_cases eq : i=j
    · exact iz eq
    · simp [span,eq] at between
  have reach : ∃ k,Walk D V i z k := by
    by_contra no
    simp [depth,no] at positive
  have visit := obtain_depth reach
  have flat : Walk D (V.erase z) j i (q+1-span D V q i j) := by
    rcases (back.mono c.sub).lastVisit z with avoid|⟨a,b,_,sum,_,rem⟩
    · exact avoid
    · exact (free i (depth D V i z+b) (by omega) (by omega)
        (visit.append (rem.mono (erase_subset _ _)))).elim
  have sub : V\K ⊆ V.erase z := by
    intro x hx
    obtain ⟨xv,xk⟩ := mem_sdiff.mp hx
    exact mem_erase.mpr ⟨fun eq => xk (eq ▸ zk),xv⟩
  have detour : Walk D (V.erase z) i j (k+2) :=
    .step (sub yu) iy ((path.mono sub).snoc (mem_erase.mpr ⟨jz,c.sub jc⟩) pj)
  have longer := strict_detour hq free mandatory
    (show span D V q i j+(q+1-span D V q i j)=q+1 by omega) (by omega : 0<k+2) detour flat
  exact ⟨pos,by omega,front⟩

/-- The exterior-walk hypothesis for simultaneous bypass, uniform in the
choice of both endpoints. On the diagonal the witness is a full turn. -/
theorem independent_excursions {D V C K J q} (hq : 1≤q) (free : QFree D V q)
    (c : Cycle D V q C) (kc : K⊆C) (jk : J⊆K)
    (equal : ∀ i∈J, ∀ z∈K, Forces D V q i z)
    (separated : ∀ i∈J, ∀ j∈J, ∃ z∈K, 0<depth D V i z ∧ depth D V i z<span D V q i j) :
    ∀ i∈J, ∀ j∈J, ∀ y∈V\K, ∀ p∈V\K, D i y=true → D p j=true →
      ∀ k, Walk D (V\K) y p k →
        ∃ d, 1≤d ∧ d≤k+1 ∧ Walk D V i j d := by
  intro i hi j hj y yu p _ iy pj k path
  obtain ⟨z,zk,pos,between⟩ := separated i hi j hj
  obtain ⟨one,short,ref⟩ := excursion_bound hq free c (kc (jk hi)) (kc (jk hj))
    zk (equal i hi z zk) pos between yu iy pj path
  exact ⟨_,one,short,ref.mono c.sub⟩

#print axioms closed_cycle_through
#print axioms strict_detour
#print axioms segments
#print axioms excursion_bound
#print axioms independent_excursions
end LeanCH.BR.Closure.MandatoryExcursion
