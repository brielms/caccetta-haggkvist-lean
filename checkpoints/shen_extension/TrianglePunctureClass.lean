import checkpoints.shen_extension.WeightedOneVertexSplit

namespace LeanCH.BR.Closure.TrianglePunctureClass
open Finset BRq2 BRq3 BR45 ShortestCycleClasses ClassParentBanks ShortestCycleWeights

private theorem on_cycle {D V q M a b} (hq : 2≤q) (hf : QFree D V q)
    (mv : M⊆V) (size : M.card=q+1) (one : OutEq 1 D M) (am : a∈M) (bm : b∈M) :
    ∃k,Walk D M a b k := by
  classical
  let U := M.filter (fun x => ∃k,Walk D M a x k)
  have sub : U⊆M := filter_subset _ _
  have deg (x) (xu : x∈U) : 1≤(outN D U x).card := by
    obtain ⟨j,p⟩ := (mem_filter.mp xu).2
    obtain ⟨z,zh⟩ := card_pos.mp (by rw [one x (sub xu)]; decide : 0<(outN D M x).card)
    obtain ⟨zm,xz⟩ := mem_outN.mp zh
    exact card_pos.mpr ⟨z,mem_outN.mpr ⟨mem_filter.mpr ⟨zm,j+1,p.snoc zm xz⟩,xz⟩⟩
  have ord := dt_size (by omega : 1≤q) (ball_q_one q (by omega)) (hf.mono_set (sub.trans mv))
    deg (show U.Nonempty from ⟨a,mem_filter.mpr ⟨am,0,.refl _⟩⟩)
  have eq := eq_of_subset_of_card_le sub (by simpa only [size,Nat.mul_one] using ord)
  exact (mem_filter.mp (show b∈U from eq.symm ▸ bm)).2

private theorem linked_walk {D V q a b} (hq : 2≤q) (hf : QFree D V q)
    (rel : Relation.EqvGen (Together D V q) a b) :
    carrier D V q a=carrier D V q b ∧
    (∃k,Walk D (carrier D V q a) a b k) ∧ (∃k,Walk D (carrier D V q a) b a k) := by
  classical
  induction rel with
  | rel a b h =>
    obtain ⟨M,mv,sz,one,am,bm⟩ := h
    have sub : M⊆carrier D V q a := fun z zm =>
      mem_filter.mpr ⟨mv zm,.rel _ _ ⟨M,mv,sz,one,am,zm⟩⟩
    obtain ⟨i,p⟩ := on_cycle hq hf mv sz one am bm
    obtain ⟨j,r⟩ := on_cycle hq hf mv sz one bm am
    exact ⟨same_class ⟨M,mv,sz,one,am,bm⟩,⟨i,p.mono sub⟩,j,r.mono sub⟩
  | refl a => exact ⟨rfl,⟨0,.refl _⟩,0,.refl _⟩
  | symm a b _ ih => exact ⟨ih.1.symm,ih.1 ▸ ih.2.2,ih.1 ▸ ih.2.1⟩
  | trans a b c _ _ ab bc =>
    obtain ⟨i,p⟩ := ab.2.1
    obtain ⟨j,r⟩ := bc.2.1
    obtain ⟨k,s⟩ := bc.2.2
    obtain ⟨m,t⟩ := ab.2.2
    exact ⟨ab.1.trans bc.1,⟨_,p.append (ab.1.symm ▸ r)⟩,_,(ab.1.symm ▸ s).append t⟩

private theorem two {D V x y k} (ne : x≠y) (no : ¬D x y=true)
    (le : k≤2) (path : Walk D V x y k) : Walk D V x y 2 := by
  have len : k=2 := by
    cases path with
    | refl => contradiction
    | step zv xz tail =>
      cases tail with
      | refl => contradiction
      | step => omega
  exact len ▸ path

private theorem first_in {n} (X : Model 3 n) {p h z} (pv : p∈X.V) (_hv : h∈X.V)
    (ph : X.D p h=true) (zw : z∈X.V\{h}) (pz : X.D p z=true) :
    z∈carrier X.D (X.V\{h}) 3 p := by
  classical
  obtain ⟨M,c,pm,zm⟩ := edge_cycle X (by decide) pv (mem_sdiff.mp zw).1 pz
  have sub : M⊆X.V\{h} := by
    intro a am
    apply mem_sdiff.mpr
    refine ⟨c.sub am,?_⟩
    rintro ah
    have hm : h∈M := mem_singleton.mp ah ▸ am
    have eq := card_le_one.mp (c.heads p pm).le h (mem_outN.mpr ⟨hm,ph⟩)
      z (mem_outN.mpr ⟨zm,pz⟩)
    exact (mem_sdiff.mp zw).2 (mem_singleton.mpr eq.symm)
  exact mem_filter.mpr ⟨zw,.rel _ _ ⟨M,sub,c.size,c.heads,pm,zm⟩⟩

private theorem parents {n} (X : Model 3 n) {r p h} (rv : r∈X.V) (pv : p∈X.V) (hv : h∈X.V)
    (rh : X.D r h=true) (ph : X.D p h=true) : p∈carrier X.D (X.V\{h}) 3 r := by
  classical
  let W := X.V\{h}
  have retained {a} (av : a∈X.V) (ah : X.D a h=true) : a∈W :=
    mem_sdiff.mpr ⟨av,fun eq => loopfree X.free (by decide) hv ((mem_singleton.mp eq) ▸ ah)⟩
  have rwv := retained rv rh
  have pw := retained pv ph
  by_cases eq : r=p
  · exact eq ▸ contains rwv
  by_cases rp : X.D r p=true
  · exact first_in X rv hv rh pw rp
  by_cases pr : X.D p r=true
  · rw [←class_eq (first_in X pv hv ph rwv pr)]
    exact contains pw
  obtain ⟨_,m,ms,back⟩ := mem_ball.mp (X.sat p pv r rv rp)
  obtain ⟨_,k,ks,fwd⟩ := mem_ball.mp (X.sat r rv p pv pr)
  have u := DeleteRepair.head_avoided X.free hv ph (two eq rp ks fwd) (by decide)
  have v := DeleteRepair.head_avoided X.free hv rh (two (Ne.symm eq) pr ms back) (by decide)
  obtain ⟨z,first,_,zp⟩ := u.unsnoc
  cases first with
  | step zw rz tail =>
    cases tail
    have safe := X.free.mono_set (sdiff_subset (t:={h}))
    obtain ⟨M,c,rm,_,pm⟩ := ShenCycleSuccessor.marked_cycle (by decide : 2≤3) safe zw pw rz zp
      (DeleteRepair.head_avoided safe zw rz v (by decide))
    exact mem_filter.mpr ⟨pw,.rel _ _ ⟨M,c.sub,c.size,c.heads,rm,pm⟩⟩

/-- In a triangle countermodel the punctured class of the parents contains
every parent, and no actual retained arc leaves this class. -/
theorem closed {n} (X : Model 3 n) {r h} (rv : r∈X.V) (hv : h∈X.V) (rh : X.D r h=true) :
    let W := X.V\{h}
    let C := carrier X.D W 3 r
    (∀p∈X.V, X.D p h=true → p∈C) ∧ ∀a∈C,outN X.D W a⊆C := by
  classical
  intro W C
  refine ⟨fun _ pv ph => parents X rv pv hv rh ph,?_⟩
  intro a ac z zh
  obtain ⟨zw,az⟩ := mem_outN.mp zh
  by_contra outside
  have safe : QFree X.D W 3 := X.free.mono_set sdiff_subset
  have nozh : ¬X.D z h=true := fun e => outside (parents X rv (mem_sdiff.mp zw).1 hv rh e)
  have back {b} (bw : b∈W) (miss : ¬X.D b z=true) : ∃k≤2,Walk X.D W z b k := by
    obtain ⟨_,m,le,path⟩ := mem_ball.mp (X.sat z (mem_sdiff.mp zw).1 b (mem_sdiff.mp bw).1 miss)
    have cut {j c} (walk : Walk X.D X.V z c j) (small : j≤2) (cw : c∈W) : Walk X.D W z c j := by
      cases walk with
      | refl => exact .refl _
      | @step _ i _ _ iv zi tail =>
        have iw : i∈W := mem_sdiff.mpr ⟨iv,fun eq => nozh (by simpa only [mem_singleton.mp eq] using zi)⟩
        cases tail with
        | refl => exact .step iw zi (.refl _)
        | step jv ij tail =>
          cases tail with
          | refl => exact .step iw zi (.step cw ij (.refl _))
          | step => omega
    exact ⟨m,le,cut path le bw⟩
  have prop {b c} (bc : b∈C) (cc : c∈C) (edge : X.D b c=true) (cz : X.D c z=true) :
      X.D b z=true := by
    by_contra miss
    obtain ⟨k,le,path⟩ := back (mem_filter.mp bc).1 miss
    have len : k=2 := by
      by_contra ne
      exact safe b (k+1+1) (by omega) (by omega) (.step (mem_filter.mp cc).1 edge (.step zw cz path))
    subst k
    obtain ⟨M,cy,bm,_,zm⟩ := ShenCycleSuccessor.marked_cycle (by decide : 2≤3) safe
      (mem_filter.mp cc).1 zw edge cz
      (DeleteRepair.head_avoided safe (mem_filter.mp cc).1 edge path (by decide))
    apply outside
    rw [show C=carrier X.D W 3 b from class_eq bc]
    exact mem_filter.mpr ⟨zw,.rel _ _ ⟨M,cy.sub,cy.size,cy.heads,bm,zm⟩⟩
  have rwv : r∈W := mem_sdiff.mpr ⟨rv,fun eq => loopfree X.free (by decide) hv ((mem_singleton.mp eq) ▸ rh)⟩
  obtain ⟨k,path⟩ := (linked_walk (by decide : 2≤3) safe (mem_filter.mp ac).2).2.1
  have push {u v j} (p : Walk X.D C u v j) (uc : u∈C) (vz : X.D v z=true) : X.D u z=true := by
    induction p with
    | refl => exact vz
    | step wc uw _ ih => exact prop uc wc uw (ih wc vz)
  exact outside (first_in X rv hv rh zw (push path (contains rwv) az))

#print axioms closed
end LeanCH.BR.Closure.TrianglePunctureClass
