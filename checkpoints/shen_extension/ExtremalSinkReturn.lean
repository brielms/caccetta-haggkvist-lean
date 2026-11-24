import checkpoints.shen_extension.OneSpareShellEscape
namespace LeanCH.BR.ExtremalSinkReturn
open Finset BRq2 BRq3 BR45 BRsGen SinkReturnAncestors

/-- At the last allowable depth a returning head fixes a unique target.
Every other vertex lies on the same shortest path to a sink. The target
heads every label of the opposite bank except the returning label. -/
theorem single_port {D V A Z q r z a} (free : QFree D V q) (av : A⊆V) (zv : Z⊆V)
    (apart : Disjoint A Z) (room : A.card≤q)
    (quota : ∀v∈A,r≤(outN D (A∪Z) v).card) (width : Z.card≤r)
    (zm : z∈Z) (am : a∈A) (za : D z a=true) (hq : 2≤q) :
    (∀v∈Z,∀x∈A,D v x=true → v=z ∧ x=a) ∧ Z.erase z⊆outN D V a := by
  classical
  have cover s (sm : s∈A) (last : Sink D A s) : Z⊆outN D V s := by
    have empty : outN D A s=∅ := eq_empty_iff_forall_notMem.mpr (fun b bm=>last b (outN_subset bm) (mem_outN.mp bm).2)
    have deg := quota s sm
    rw [card_outN_union apart,empty,card_empty,zero_add] at deg
    have eq : outN D Z s=Z := eq_of_subset_of_card_le outN_subset (by omega)
    exact eq ▸ (outN_mono zv s : outN D Z s⊆outN D V s)
  obtain ⟨p⟩ := exists_shortest_sink_path (free.mono_set av) room am
  let s := p.vertex p.len
  have sm : s∈A := p.mem _ le_rfl
  have route : Walk D V a s p.len := by
    simpa only [p.start,Nat.sub_zero] using (p.walk (Nat.zero_le _) le_rfl).mono av
  have large : q<p.len+2 := by
    by_contra! le
    exact free a _ (by omega) (by omega) ((route.snoc (zv zm) (mem_outN.mp (cover s sm p.sink zm)).2).snoc (av am) za)
  have less := p.bounded
  have onto : (range (p.len+1)).image p.vertex=A := by
    apply eq_of_subset_of_card_le
    · intro x xm
      obtain ⟨i,im,rfl⟩ := mem_image.mp xm
      exact p.mem i (Nat.le_of_lt_succ (mem_range.mp im))
    · rw [card_image_of_injOn (p.injective (free.mono_set av) room),card_range]; omega
  have unique v (vm : v∈Z) x (xm : x∈A) (arc : D v x=true) : x=a := by
    obtain ⟨i,im,eq⟩ := mem_image.mp (onto.symm ▸ xm)
    have le := mem_range.mp im
    by_cases zero : i=0
    · subst i; exact eq.symm.trans p.start
    · have tail := (p.walk (show i≤p.len by omega) le_rfl).mono av
      exact (free (p.vertex i) _ (by omega) (by omega)
        ((tail.snoc (zv vm) (mem_outN.mp (cover s sm p.sink vm)).2).snoc
          (av (p.mem i (by omega))) (eq.symm ▸ arc))).elim
  have d := SinkTransit.internal_depth (free.mono_set av) room p
  have deg := quota a am
  rw [card_outN_union apart] at deg
  have own : z∉outN D Z a := fun hit=>free a 2 (by decide) hq
    (.step (zv zm) (mem_outN.mp hit).2 (.step (av am) za (.refl a)))
  have heads : outN D Z a=Z.erase z := by
    apply eq_of_subset_of_card_le (fun v vm=>mem_erase.mpr ⟨fun (eq : v=z)=>own (eq ▸ vm),outN_subset vm⟩)
    rw [card_erase_of_mem zm]; omega
  have all := heads ▸ (outN_mono zv a : outN D Z a⊆outN D V a)
  refine ⟨?_,all⟩
  intro v vm x xm arc
  obtain rfl := unique v vm x xm arc
  refine ⟨?_,rfl⟩
  by_contra ne
  exact free x 2 (by decide) hq (.step (zv vm) (mem_outN.mp (all (mem_erase.mpr ⟨ne,vm⟩))).2 (.step (av xm) arc (.refl x)))

/-- If a sink of A fills Z and Z can exit only through A or W, all r
heads of an actual Z row land in W, even when A has q vertices. -/
theorem exit_bank {D V A Z W q r} (free : QFree D V q) (av : A⊆V) (zv : Z⊆V)
    (apart : Disjoint A Z) (room : A.card≤q)
    (quota : ∀v∈A,r≤(outN D (A∪Z) v).card) (width : Z.card=r) (time : r≤q) (hr : 3≤r)
    (row : ∀z∈Z,outN D V z⊆(A∪Z)∪W) (degree : ∀z∈Z,r≤(outN D V z).card) : r≤W.card := by
  classical
  have small : Z.card≤q := by omega
  by_cases returns : ∃z∈Z,∃a∈A,D z a=true
  · obtain ⟨z,zm,a,am,za⟩ := returns
    have ⟨only,heads⟩ := single_port free av zv apart room quota width.le zm am za (by omega)
    have k := card_erase_add_one zm
    obtain ⟨s,sm,stop⟩ := exists_sink (free.mono_set ((erase_subset z Z).trans zv))
      (card_pos.mp (by omega)) (by omega)
    have ⟨ne,sz⟩ := mem_erase.mp sm
    have out : outN D V s⊆W := by
      intro b bm
      apply (mem_union.mp (row s sz bm)).resolve_left
      intro early
      have arc := (mem_outN.mp bm).2
      rcases mem_union.mp early with ba|bz
      · exact ne (only s sz b ba arc).1
      · by_cases eq : b=z
        · subst b
          exact free a 3 (by decide) (by omega) (.step (zv sz) (mem_outN.mp (heads sm)).2
            (.step (zv zm) arc (.step (av am) za (.refl a))))
        · exact stop b (mem_erase.mpr ⟨eq,bz⟩) arc
    exact (degree s sz).trans (card_le_card out)
  · obtain ⟨s,sm,stop⟩ := exists_sink (free.mono_set zv) (card_pos.mp (by omega)) small
    have out : outN D V s⊆W := by
      intro b bm
      apply (mem_union.mp (row s sm bm)).resolve_left
      intro early
      rcases mem_union.mp early with ba|bz
      · exact returns ⟨s,sm,b,ba,(mem_outN.mp bm).2⟩
      · exact stop b bz (mem_outN.mp bm).2
    exact (degree s sm).trans (card_le_card out)

attribute [aesop safe forward (immediate := [free,av,zv,apart,room,quota,width,zm,am,za,hq]) (rule_sets := [CHGraphFamilies])] single_port
attribute [aesop safe forward (immediate := [free,av,zv,apart,room,quota,width,time,hr,row,degree]) (rule_sets := [CHGraphFamilies])] exit_bank
#print axioms single_port
#print axioms exit_bank
end LeanCH.BR.ExtremalSinkReturn
