import checkpoints.shen_extension.ShortestCycleWeights

namespace LeanCH.BR.Closure.PuncturedSquareRoles
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor ShortestCycleWeights

inductive Role where | head | opposite | parent deriving DecidableEq

def role (D : CH.Digraph) (h x : ℕ) : Role :=
  if D h x=true then .head else if D x h=true then .parent else .opposite

theorem parent_role {n} (X : Model 3 n) {h x} (hv : h∈X.V) (xv : x∈X.V)
    (xh : X.D x h=true) : role X.D h x=.parent := by
  simp [role,Bool.eq_false_iff.mpr (digonfree X.free (by decide) xv hv xh),xh]

theorem head_role {D h x} (hx : D h x=true) : role D h x=.head := by simp [role,hx]

theorem head_arc {D h x} (r : role D h x=.head) : D h x=true := by
  by_contra no
  simp [role,no] at r
  split at r <;> contradiction

private theorem roles {n} (X : Model 3 n) {M h r t} (c : Cycle X.D X.V 3 M)
    (hm : h∈M) (rm : r∈M) (tm : t∈M) (rh : r≠h) (th : t≠h) (rt : r≠t) :
    role X.D h r≠role X.D h t ∧
    (role X.D h r=.head → role X.D h t=.opposite → X.D r t=true) ∧
    (role X.D h r=.opposite → role X.D h t=.parent → X.D r t=true) := by
  classical
  let D := X.D
  have next (i) (im : i∈M) : ∃j∈M,D i j=true := by
    obtain ⟨j,jh⟩ := card_pos.mp (by rw [c.heads i im]; decide : 0<(outN D M i).card)
    exact ⟨j,mem_outN.mp jh⟩
  obtain ⟨o,om,ho⟩ := next h hm
  obtain ⟨z,zm,oz⟩ := next o om
  have ic : (inN D M h).card=1 := c.incoming h hm
  obtain ⟨p,pi⟩ := card_pos.mp (show 0<(inN D M h).card by omega)
  obtain ⟨pm,ph⟩ := mem_inN.mp pi
  have loop (i) (im : i∈M) : ¬D i i=true := loopfree X.free (by decide) (c.sub im)
  have zh : ¬D z h=true := fun edge => X.free h 3 (by decide) le_rfl
    (.step (c.sub om) ho (.step (c.sub zm) oz (.step (c.sub hm) edge (.refl _))))
  have hnz : ¬D h z=true := by
    intro hz
    have e := card_le_one.mp (c.heads h hm).le z (mem_outN.mpr ⟨zm,hz⟩) o (mem_outN.mpr ⟨om,ho⟩)
    exact loop o om (e ▸ oz)
  have oh : ¬D o h=true := digonfree X.free (by decide) (c.sub hm) (c.sub om) ho
  have zo : ¬D z o=true := digonfree X.free (by decide) (c.sub om) (c.sub zm) oz
  have ro := head_role ho
  have rp := parent_role X (c.sub hm) (c.sub pm) ph
  have rz : role D h z=.opposite := by simp [role,hnz,zh]
  have noH : o≠h := fun e => loop h hm (e ▸ ho)
  have nzH : z≠h := fun e => oh (e ▸ oz)
  have npH : p≠h := fun e => loop h hm (e ▸ ph)
  have noz : o≠z := fun e => loop z zm (e ▸ oz)
  have nop : o≠p := fun e => oh (e.symm ▸ ph)
  have nzp : z≠p := fun e => zh (e.symm ▸ ph)
  have full : ({h,o,z,p}:Finset ℕ)=M := eq_of_subset_of_card_le
    (insert_subset hm (insert_subset om (insert_subset zm (singleton_subset_iff.mpr pm))))
    (by rw [c.size]; simp [Ne.symm noH,Ne.symm nzH,Ne.symm npH,noz,nop,nzp])
  have loc (y) (ym : y∈M) (yh : y≠h) : y=o ∨ y=z ∨ y=p := by
    rw [←full] at ym
    simpa [yh] using ym
  obtain ⟨j,jm,zj⟩ := next z zm
  have jh : j≠h := fun e => zh (e ▸ zj)
  have jp : j=p := (loc j jm jh).resolve_left (fun e => zo (e ▸ zj)) |>.resolve_left
    (fun e => loop z zm (e ▸ zj))
  have zp : D z p=true := jp ▸ zj
  change role D h p=.parent at rp
  change role D h r≠role D h t ∧ _ at ⊢
  rcases loc r rm rh with rfl|rfl|rfl <;> rcases loc t tm th with e|e|e <;>
    subst t <;> simp_all [D]

/-- If two retained labels have no common retained square, all their
original common squares pass through the root and fix their relative roles. -/
theorem forced {n} (X : Model 3 n) {h r t} (rv : r∈X.V) (tv : t∈X.V)
    (rh : r≠h) (th : t≠h) (rt : r≠t)
    (miss : ¬∃M,Cycle X.D (X.V\{h}) 3 M ∧ r∈M ∧ t∈M) :
    role X.D h r≠role X.D h t ∧
    (role X.D h r=.head → role X.D h t=.opposite → X.D r t=true) ∧
    (role X.D h r=.opposite → role X.D h t=.parent → X.D r t=true) := by
  obtain ⟨M,c,rm,tm⟩ := pair_four X rv tv rt
  have hm : h∈M := by
    by_contra absent
    exact miss ⟨M,⟨fun x xm => mem_sdiff.mpr ⟨c.sub xm,fun e => absent (mem_singleton.mp e ▸ xm)⟩,
      c.size,c.heads,c.incoming⟩,rm,tm⟩
  exact roles X c hm rm tm rh th rt

/-- A head of h on an original square has a next vertex opposite h. -/
theorem head_next {n} (X : Model 3 n) {h t} (hv : h∈X.V) (tv : t∈X.V) (ht : X.D h t=true) :
    ∃z∈X.V, z≠h ∧ role X.D h z=.opposite ∧ X.D t z=true := by
  obtain ⟨M,c,hm,tm⟩ := edge_cycle X (by decide) hv tv ht
  obtain ⟨z,zin⟩ := card_pos.mp (by rw [c.heads t tm]; decide : 0<(outN X.D M t).card)
  obtain ⟨zm,tz⟩ := mem_outN.mp zin
  have zh : ¬X.D z h=true := fun edge => X.free h 3 (by decide) le_rfl
    (.step tv ht (.step (c.sub zm) tz (.step hv edge (.refl _))))
  have no : z≠h := fun e => digonfree X.free (by decide) hv tv ht (e ▸ tz)
  have hz : ¬X.D h z=true := by
    intro arc
    have e := card_le_one.mp (c.heads h hm).le z (mem_outN.mpr ⟨zm,arc⟩) t (mem_outN.mpr ⟨tm,ht⟩)
    exact loopfree X.free (by decide) tv (e ▸ tz)
  exact ⟨z,c.sub zm,no,by simp [role,hz,zh],tz⟩

#print axioms forced
#print axioms head_next
end LeanCH.BR.Closure.PuncturedSquareRoles
