import checkpoints.shen_extension.StoppedParentHall

namespace LeanCH.BR.Closure.FiniteHorizonHall
open Finset BRq2 BRq3 BR45 BRsub WeightedSD

/-- A radius-(q-1) union of balls containing all but at most one label
is the only exception to strict q-fold mass growth on a strict source. -/
theorem ball_growth {q E V z} {c : ℝ} (hq : 2≤q) (high : 1<c) (small : SmallerSmallRow q V.card)
    (free : QFree E V q) (unit : realMass V z=1) (pos : ∀i∈V,0<z i)
    (rows : ∀i∈V,realRow q E V z i=c) {O : Finset ℕ} (os : O⊆V) (on : O.Nonempty)
    (room : (ballSet E V O (q-1)).card+1<V.card) :
    (q:ℝ)*realMass O z<realMass (ballSet E V O (q-1)) z := by
  classical
  let J := ballSet E V O (q-1)
  let I := J.filter (fun i => ∃x∈V\J,E i x=true)
  have js : J⊆V := by
    intro i hi
    obtain ⟨o,_,ho⟩ := mem_ballSet.mp hi
    exact (mem_ball.mp ho).1
  have oj : O⊆J := fun o ho => mem_ballSet.mpr ⟨o,ho,mem_ball.mpr ⟨os ho,0,Nat.zero_le _,.refl _⟩⟩
  have part : J⊂V := Finset.ssubset_iff_subset_ne.mpr ⟨js,fun e => by
    change J.card+1<V.card at room
    rw [e] at room
    omega⟩
  obtain ⟨y,_,fresh⟩ := exists_of_ssubset part
  let F := coreTwoSidedExtension E J I O y
  have safe : QFree F (insert y J) q := by
    apply coreTwoSidedExtension_qfree fresh (filter_subset _ _) (free.mono_set js)
    intro o ho i hi k hk path
    obtain ⟨_,x,hx,ed⟩ := mem_filter.mp hi
    have tail : Walk E V i x 1 := .step (mem_sdiff.mp hx).1 ed (.refl _)
    exact (mem_sdiff.mp hx).2 (mem_ballSet.mpr ⟨o,ho,mem_ball.mpr
      ⟨(mem_sdiff.mp hx).1,k+1,by omega,(path.mono js).append tail⟩⟩)
  have old (i) (hi : i∈J) (j) (hj : j∈J) : F i j=E i j := by
    have iv : i≠y := fun eq => fresh (eq ▸ hi)
    have jv : j≠y := fun eq => fresh (eq ▸ hj)
    simp [F,coreTwoSidedExtension,coreOutgoingExtension,hi,hj,iv,jv]
  have cut (i) (hi : i∈J) (x) (hx : x∈V\J) (ed : E i x=true) : F i y=true :=
    decide_eq_true (Or.inr ⟨mem_filter.mpr ⟨hi,x,hx,ed⟩,rfl⟩)
  have bd := SlackBoundaryBanks.fold_comparison high.le hq small unit pos rows part fresh room safe old cut
  have lt := lt_of_le_of_ne bd.1 (fun eq => high.ne' ((bd.2 eq).1 (on.mono oj)))
  have heads (i) (hi : i∈J) : F y i=true ↔ i∈O := by
    have iy : i≠y := fun eq => fresh (eq ▸ hi)
    simp [F,coreTwoSidedExtension,coreOutgoingExtension,hi,fresh,iy]
  have out : realOutW F J z y=realMass O z := by
    unfold realOutW realMass
    rw [sum_congr rfl (fun i hi => if_congr (heads i hi) rfl rfl),←sum_filter]
    congr 1
    ext i
    exact mem_filter.trans (and_iff_right_of_imp (fun h => oj h))
  rwa [out] at lt

/-- The actual heads of the root which can reach at least one selected target
with at most q-1 more arcs. -/
noncomputable def ports (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (y : ℕ) (K : Finset ℕ) : Finset ℕ := by
  classical
  exact (outN E V y).filter (fun h => ∃k∈K,k∈ball E V h (q-1))

theorem capacity {q E V z} {c : ℝ} (hq : 2≤q) (high : 1<c) (small : SmallerSmallRow q V.card)
    (free : QFree E V q) (unit : realMass V z=1) (pos : ∀i∈V,0<z i)
    (rows : ∀i∈V,realRow q E V z i=c) {y} (yv : y∈V) {K : Finset ℕ}
    (ks : K⊆V.erase y) (kn : K.Nonempty) :
    realMass K z+(c-1)≤(q:ℝ)*realMass (ports q E V y K) z ∧
    (K≠V.erase y → realMass K z+(c-1)<(q:ℝ)*realMass (ports q E V y K) z) := by
  classical
  let P := ports q E V y K
  let O := outN E V y\P
  let J := ballSet E V O (q-1)
  let U := V.erase y
  let L := U\K
  have os : O⊆V := fun i hi => (mem_outN.mp (mem_sdiff.mp hi).1).1
  have js : J⊆L := by
    intro i hi
    obtain ⟨o,ho,reach⟩ := mem_ballSet.mp hi
    obtain ⟨iv,k,le,path⟩ := mem_ball.mp reach
    have ed := mem_outN.mp (mem_sdiff.mp ho).1
    refine mem_sdiff.mpr ⟨mem_erase.mpr ⟨?_,iv⟩,fun h => (mem_sdiff.mp ho).2 (mem_filter.mpr
      ⟨(mem_sdiff.mp ho).1,i,h,reach⟩)⟩
    rintro rfl
    exact free i (k+1) (by omega) (by omega) (.step ed.1 ed.2 path)
  have lu : L⊂U := Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset,fun e => by
    obtain ⟨k,hk⟩ := kn
    exact (mem_sdiff.mp (show k∈L from e.symm ▸ ks hk)).2 hk⟩
  have room : J.card+1<V.card := by
    have := card_le_card js
    have := card_lt_card lu
    have u : U.card+1=V.card := card_erase_add_one yv
    omega
  have bounds : (q:ℝ)*realMass O z≤realMass L z ∧ (L.Nonempty → (q:ℝ)*realMass O z<realMass L z) := by
    by_cases on : O.Nonempty
    · have lt := ball_growth hq high small free unit pos rows os on room
      have le : realMass J z≤realMass L z := sum_le_sum_of_subset_of_nonneg js
        (fun i hi _ => (pos i (mem_erase.mp (mem_sdiff.mp hi).1).2).le)
      exact ⟨lt.le.trans le,fun _ => lt.trans_le le⟩
    · have zero : realMass O z=0 := by simp [realMass,not_nonempty_iff_eq_empty.mp on]
      rw [zero,mul_zero]
      have pp (i) (hi : i∈L) := pos i (mem_erase.mp (mem_sdiff.mp hi).1).2
      exact ⟨sum_nonneg (fun i hi => (pp i hi).le),fun live => sum_pos pp live⟩
  have split : realMass O z+realMass P z=realOutW E V z y := by
    unfold realMass realOutW
    rw [show O=outN E V y\P from rfl,sum_sdiff (show P⊆outN E V y from filter_subset _ _)]
    simp only [outN,sum_filter]
  have mass : realMass L z+realMass K z+z y=1 := by
    change (∑i∈U\K,z i)+(∑i∈K,z i)+z y=1
    rw [sum_sdiff ks,sum_erase_add V z yv]; exact unit
  have r := rows y yv
  rw [realRow,←split,mul_add] at r
  refine ⟨by linarith [bounds.1],?_⟩
  intro ne
  have live : L.Nonempty := sdiff_nonempty.mpr (fun sub => ne (Subset.antisymm ks sub))
  linarith [bounds.2 live]

#print axioms ball_growth
#print axioms capacity
noncomputable def cyclePorts (E : CH.Digraph) (V : Finset ℕ) (F : Finset (Finset ℕ))
    (y : ℕ) (K : Finset ℕ) : Finset ℕ := by
  classical
  exact (outN E V y).filter (fun h => ∃k∈K,∃M∈F,k∈M ∧ y∈M ∧ h∈M)

theorem marked_of_port {q E V y k o} (hq : 2≤q) (free : QFree E V q) (yv : y∈V)
    (oh : o∈outN E V y) (kh : k∈inN E V y) (hit : k∈ball E V o (q-1)) :
    ∃M,ShenCycleSuccessor.Cycle E V q M ∧ k∈M ∧ y∈M ∧ o∈M := by
  obtain ⟨_,n,le,path⟩ := mem_ball.mp hit
  have oe := mem_outN.mp oh
  have ke := mem_inN.mp kh
  have edge : Walk E V k y 1 := .step yv ke.2 (.refl _)
  have full : n=q-1 := by
    by_contra diff
    exact free y (n+1+1) (by omega) (by omega) ((Walk.step oe.1 oe.2 path).append edge)
  have clean : Walk E (V.erase y) o k n := by
    rcases path.lastVisit y with ok|⟨m,l,_,sz,early,_⟩
    · exact ok
    · exact (free y (m+1) (by omega) (by omega) (.step oe.1 oe.2 early)).elim
  exact ShenCycleSuccessor.marked_cycle hq free yv oe.1 ke.2 oe.2 (by simpa only [sdiff_singleton_eq_erase,←full] using clean)

/-- For sets of parents the finite horizon forces equality of the return
length. Every charged head is realized on a shortest cycle in F. -/
theorem cycle_capacity {q E V z F} {c : ℝ} (hq : 2≤q) (high : 1<c) (small : SmallerSmallRow q V.card)
    (free : QFree E V q) (unit : realMass V z=1) (pos : ∀i∈V,0<z i)
    (rows : ∀i∈V,realRow q E V z i=c)
    (complete : ∀M,ShenCycleSuccessor.Cycle E V q M → M∈F)
    {y} (yv : y∈V) {K : Finset ℕ} (ks : K⊆inN E V y) (kn : K.Nonempty) :
    realMass K z+(c-1)<(q:ℝ)*realMass (cyclePorts E V F y K) z := by
  classical
  have no (i) (iv : i∈V) (ed : E y i=true) (back : E i y=true) :=
    free y 2 (by omega) hq (.step iv ed (.step yv back (.refl y)))
  have loop : E y y≠true := fun ed => no y yv ed ed
  have ku : K⊆V.erase y := fun i hi => mem_erase.mpr
    ⟨fun eq => loop (eq ▸ (mem_inN.mp (ks hi)).2),(mem_inN.mp (ks hi)).1⟩
  have ex : (outN E V y).Nonempty := by
    by_contra! em
    have r := rows y yv
    have zero : realOutW E V z y=0 := by simpa only [realOutW,outN,sum_filter] using
          (show (∑i∈outN E V y,z i)=0 by rw [em,sum_empty])
    have lower : z y≤realMass V z := single_le_sum (fun i hi => (pos i hi).le) yv
    rw [realRow,zero,mul_zero,add_zero] at r
    linarith
  obtain ⟨h,hh⟩ := ex
  have ne : K≠V.erase y := by
    intro eq
    obtain ⟨hv,ed⟩ := mem_outN.mp hh
    have hk : h∈K := eq ▸ mem_erase.mpr ⟨fun e => loop (e ▸ ed),hv⟩
    exact no h hv ed (mem_inN.mp (ks hk)).2
  have sub : ports q E V y K⊆cyclePorts E V F y K := by
    intro o ho
    obtain ⟨oh,k,hk,hit⟩ := mem_filter.mp ho
    obtain ⟨M,cm,km,ym,om⟩ := marked_of_port hq free yv oh (ks hk) hit
    exact mem_filter.mpr ⟨oh,k,hk,M,complete M cm,km,ym,om⟩
  have larger : realMass (ports q E V y K) z≤realMass (cyclePorts E V F y K) z :=
    sum_le_sum_of_subset_of_nonneg sub (fun i hi _ => (pos i (mem_outN.mp (mem_filter.mp hi).1).1).le)
  exact ((capacity hq high small free unit pos rows yv ku kn).2 ne).trans_le
    (mul_le_mul_of_nonneg_left larger (Nat.cast_nonneg q))

/-- A missing rectangle of consecutive arcs on shortest cycles has a strict
budget, measured on the original vertices. -/
theorem missing_rectangle {q E V z} {F : Finset (Finset ℕ)} {c : ℝ} (hq : 2≤q) (high : 1<c) (small : SmallerSmallRow q V.card)
    (free : QFree E V q) (unit : realMass V z=1) (pos : ∀i∈V,0<z i)
    (rows : ∀i∈V,realRow q E V z i=c) (complete : ∀M,ShenCycleSuccessor.Cycle E V q M → M∈F)
    {y} (yv : y∈V) {K O : Finset ℕ} (ks : K⊆inN E V y) (kn : K.Nonempty) (os : O⊆outN E V y)
    (apart : ∀k∈K,∀o∈O,∀M∈F,k∈M → y∈M → o∉M) :
    z y+realMass K z+(q:ℝ)*realMass O z<1 := by
  classical
  let P := cyclePorts E V F y K
  have cs := cycle_capacity hq high small free unit pos rows complete yv ks kn
  have dd : Disjoint O P := disjoint_left.mpr (fun i io ip => by
    obtain ⟨_,k,hk,M,mf,km,ym,im⟩ := mem_filter.mp ip
    exact apart k hk i io M mf km ym im)
  have inside : O∪P⊆outN E V y := union_subset os (filter_subset _ _)
  have le : realMass O z+realMass P z≤realOutW E V z y := by
    unfold realMass realOutW
    rw [←sum_union dd,←sum_filter]
    exact sum_le_sum_of_subset_of_nonneg inside (fun i hi _ => (pos i (mem_outN.mp hi).1).le)
  change realMass K z+(c-1)<(q:ℝ)*realMass P z at cs
  have r := rows y yv
  unfold realRow at r
  linarith [mul_le_mul_of_nonneg_left le (Nat.cast_nonneg q : (0:ℝ)≤q),
    mul_add (q:ℝ) (realMass O z) (realMass P z)]

#print axioms marked_of_port
#print axioms cycle_capacity
#print axioms missing_rectangle
/-- A two-sided alternative on the very same parents, heads and completed
family used by the repair schedule. Both prices refer to original labels. -/
theorem rectangle_on_source {q E V} {F : Finset (Finset ℕ)} (hq : 2≤q)
    (free : QFree E V q) (small : SmallerSmallRow q V.card)
    {x p : ℕ→ℚ} {c : ℚ} (high : 1<c) (xp : ∀i∈V,0<x i) (pp : ∀i∈V,0<p i)
    (xm : mass V x=1) (pm : mass V p=1) (rows : ∀i∈V,WeightedSD.row q E V x i=c)
    (cols : ∀i∈V,WeightedSD.col q E V p i=c) (complete : ∀M,ShenCycleSuccessor.Cycle E V q M → M∈F)
    (y) (yv : y∈V) {K O : Finset ℕ} (ks : K⊆inN E V y) (kn : K.Nonempty)
    (os : O⊆outN E V y) (on : O.Nonempty) :
    (∃M∈F,y∈M ∧ (K∩M).Nonempty ∧ (O∩M).Nonempty) ∨
      (x y+mass K x+q*mass O x<1 ∧ p y+mass O p+q*mass K p<1) := by
  classical
  by_cases hit : ∃M∈F,y∈M ∧ (K∩M).Nonempty ∧ (O∩M).Nonempty
  · exact Or.inl hit
  right
  have apart (k) (hk : k∈K) (o) (ho : o∈O) (M) (mf : M∈F) (km : k∈M) (ym : y∈M) (om : o∈M) :=
    hit ⟨M,mf,ym,⟨k,mem_inter.mpr ⟨hk,km⟩⟩,⟨o,mem_inter.mpr ⟨ho,om⟩⟩⟩
  have strict : 1<(c:ℝ) := by exact_mod_cast high
  have fw := missing_rectangle (z:=fun i => (x i : ℝ)) hq strict small free
    (by rw [realMass_rat,xm]; norm_num) (fun i hi => by exact_mod_cast xp i hi)
    (fun i hi => by rw [realRow_rat,rows i hi]) complete yv ks kn os apart
  have rev (M) (cm : ShenCycleSuccessor.Cycle (fun a b => E b a) V q M) : M∈F :=
    complete M ⟨cm.sub,cm.size,cm.incoming,cm.heads⟩
  have br := missing_rectangle (z:=fun i => (p i : ℝ)) hq strict small free.reverse
    (by rw [realMass_rat,pm]; norm_num) (fun i hi => by exact_mod_cast pp i hi)
    (fun i hi => by change realCol q E V (fun i => (p i : ℝ)) i=(c:ℝ); rw [realCol_rat,cols i hi])
    rev yv os on ks (fun o ho k hk M mf om ym km => apart k hk o ho M mf km ym om)
  simp only [realMass_rat] at fw br
  exact ⟨by exact_mod_cast fw,by exact_mod_cast br⟩

#print axioms rectangle_on_source
end LeanCH.BR.Closure.FiniteHorizonHall
