import checkpoints.shen_extension.SharedArcPacketDescent

namespace LeanCH.BR.Closure.SharedArcTailExchange
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights FirstPacketBarrier
open MarkedCyclePeeling SharedArcExpansion SharedArcBarrier SharedArcPacketDescent

private theorem inserted {D F B i j} :
    graph D (insert B F) i j=true ↔ graph D F i j=true ∨ i∈B ∧ j∈B ∧ D i j=true := by
  classical
  constructor
  · intro e
    obtain ⟨M,m⟩ := active.mp e
    obtain ⟨mf,im,jm,ij⟩ := mem_col.mp m
    rcases mem_insert.mp mf with rfl|af
    · exact Or.inr ⟨im,jm,ij⟩
    · exact Or.inl (active.mpr ⟨M,mem_col.mpr ⟨af,im,jm,ij⟩⟩)
  · rintro (old|⟨ib,jb,ij⟩)
    · obtain ⟨M,m⟩ := active.mp old
      obtain ⟨mf,im,jm,ij⟩ := mem_col.mp m
      exact active.mpr ⟨M,mem_col.mpr ⟨mem_insert_of_mem mf,im,jm,ij⟩⟩
    · exact active.mpr ⟨B,mem_col.mpr ⟨mem_insert_self B F,ib,jb,ij⟩⟩

/-- At an old-to-new turn r→a→b in B, any exterior z with old r→z and
fresh native z→b gives a true competing shortest cycle. Its only change
to the child graph is to replace the tail a by z at b. -/
theorem square {q n} (X : Model q n) (hq : 2≤q) {F B} (step : Boundary X F B)
    {r a b z} (rb : r∈B) (ab : a∈B) (bb : b∈B) (zv : z∈X.V) (outside : z∉B)
    (ra : graph X.D F r a=true) (rz : graph X.D F r z=true)
    (ed : X.D a b=true) (zb : X.D z b=true)
    (offA : graph X.D F a b=false) (offZ : graph X.D F z b=false) :
    let M := insert z (B.erase a)
    Boundary X F M ∧ targets X.D X.V F M=targets X.D X.V F B ∧
      graph X.D (insert M F)=insertArc (eraseArc (graph X.D (insert B F)) a b) z b := by
  classical
  intro M
  let E := graph X.D F
  let G := graph X.D (insert B F)
  have native {i j} (h : E i j=true) : X.D i j=true := by obtain ⟨_,m⟩ := active.mp h; exact (mem_col.mp m).2.2.2
  have cb : Cycle X.D X.V q B := (mem_filter.mp step.1).2
  have rn : r≠a := fun eq => loopfree X.free (by omega) (cb.sub ab) (by simpa only [eq] using (native ra : X.D r a=true))
  have bn : b≠a := fun eq => loopfree X.free (by omega) (cb.sub ab) (eq ▸ ed)
  have za : z≠a := fun eq => outside (eq ▸ ab)
  have join {i} (ib : i∈B) (ne : i≠a) : i∈M := mem_insert_of_mem (mem_erase.mpr ⟨ne,ib⟩)
  have zm : z∈M := mem_insert_self _ _
  have oldlabel {i} (im : i∈M) (ne : i≠z) : i∈B.erase a := (mem_insert.mp im).resolve_left ne
  have mv : M⊆X.V := insert_subset zv ((erase_subset _ _).trans cb.sub)
  have size : M.card=q+1 := by
    change (insert z (B.erase a)).card=_
    rw [card_insert_of_notMem (fun h => outside (mem_of_mem_erase h)),card_erase_add_one ab,cb.size]
  have parent {i} (ib : i∈B) (ia : X.D i a=true) : i=r :=
    card_le_one.mp (cb.incoming a ab).le _ (mem_inN.mpr ⟨ib,ia⟩) _ (mem_inN.mpr ⟨rb,native ra⟩)
  have deg (i) (im : i∈M) : 1≤(outN X.D M i).card := by
    by_cases eq : i=z
    · exact card_pos.mpr ⟨b,mem_outN.mpr ⟨join bb bn,eq ▸ zb⟩⟩
    have ib := mem_of_mem_erase (oldlabel im eq)
    obtain ⟨j,jh⟩ := card_pos.mp (show 0<(outN X.D B i).card by rw [cb.heads i ib]; decide)
    obtain ⟨jb,ij⟩ := mem_outN.mp jh
    by_cases ja : j=a
    · exact card_pos.mpr ⟨z,mem_outN.mpr ⟨zm,(parent ib (ja ▸ ij)) ▸ native rz⟩⟩
    · exact card_pos.mpr ⟨j,mem_outN.mpr ⟨join jb ja,ij⟩⟩
  have reg := dt_reg (by omega : 1≤q) (ball_q_one q (by omega)) (X.free.mono_set mv) deg (by simpa using size)
  have cm : Cycle X.D X.V q M := ⟨mv,size,reg.1,reg.2⟩
  have bm := join bb bn
  have rm := join rb rn
  have stay {i j} (im : i∈M) (jm : j∈M) (ij : X.D i j=true) (no : E i j=false) :
      (i=z ∧ j=b) ∨ (i∈B.erase a ∧ j∈B.erase a) := by
    by_cases iz : i=z
    · exact Or.inl ⟨iz,card_le_one.mp (cm.heads z zm).le _ (mem_outN.mpr ⟨jm,iz ▸ ij⟩) _ (mem_outN.mpr ⟨bm,zb⟩)⟩
    have jz : j≠z := by
      intro eqj
      subst j
      have eq : i=r := card_le_one.mp (cm.incoming z zm).le _ (mem_inN.mpr ⟨im,ij⟩) _ (mem_inN.mpr ⟨rm,native rz⟩)
      exact Bool.noConfusion (no.symm.trans (eq ▸ rz))
    exact Or.inr ⟨oldlabel im iz,oldlabel jm jz⟩
  have back {i j} (ib : i∈B) (jb : j∈B) (ij : X.D i j=true) (no : E i j=false) :
      (i=a ∧ j=b) ∨ (i∈M ∧ j∈M) := by
    by_cases ia : i=a
    · exact Or.inl ⟨ia,card_le_one.mp (cb.heads a ab).le _ (mem_outN.mpr ⟨jb,ia ▸ ij⟩) _ (mem_outN.mpr ⟨bb,ed⟩)⟩
    have ja : j≠a := by rintro rfl; exact Bool.noConfusion (no.symm.trans ((parent ib ij) ▸ ra))
    exact Or.inr ⟨join ib ia,join jb ja⟩
  have absent : M∉F := fun mf => Bool.noConfusion (offZ.symm.trans (active.mpr ⟨M,mem_col.mpr ⟨mf,zm,bm,zb⟩⟩))
  obtain ⟨A,hit⟩ := active.mp rz
  obtain ⟨af,ar,az,arc⟩ := mem_col.mp hit
  refine ⟨⟨mem_filter.mpr ⟨mem_powerset.mpr mv,cm⟩,absent,A,af,r,mem_inter.mpr ⟨ar,rm⟩,z,mem_inter.mpr ⟨az,zm⟩,arc⟩,?_,?_⟩
  · ext j
    constructor
    · intro h
      obtain ⟨vv,jm,i,im,ij,no⟩ := mem_filter.mp h
      rcases stay im jm ij no with ⟨rfl,rfl⟩|⟨ib,jb⟩
      · exact mem_filter.mpr ⟨vv,bb,a,ab,ed,offA⟩
      · exact mem_filter.mpr ⟨vv,mem_of_mem_erase jb,i,mem_of_mem_erase ib,ij,no⟩
    · intro h
      obtain ⟨vv,jb,i,ib,ij,no⟩ := mem_filter.mp h
      rcases back ib jb ij no with ⟨rfl,rfl⟩|⟨im,jm⟩
      · exact mem_filter.mpr ⟨vv,bm,z,zm,zb,offZ⟩
      · exact mem_filter.mpr ⟨vv,jm,i,im,ij,no⟩
  · funext i j
    by_cases atZ : i=z ∧ j=b
    · obtain ⟨rfl,rfl⟩ := atZ
      simp only [insertArc,eq_self,and_self,ite_true]
      exact inserted.mpr (Or.inr ⟨zm,bm,zb⟩)
    by_cases atA : i=a ∧ j=b
    · obtain ⟨eqi,eqj⟩ := atA
      subst i
      subst j
      have am : a∉M := fun h => (mem_erase.mp (oldlabel h za.symm)).1 rfl
      simp [insertArc,eraseArc,Ne.symm za]
      apply Bool.eq_false_iff.mpr
      intro h
      rcases inserted.mp h with yes|here
      · exact Bool.noConfusion (offA.symm.trans yes)
      · exact am here.1
    simp only [insertArc,atZ,ite_false,eraseArc,atA]
    apply Bool.eq_iff_iff.mpr
    by_cases old : E i j=true
    · exact ⟨fun _ => inserted.mpr (Or.inl old),fun _ => inserted.mpr (Or.inl old)⟩
    have no := Bool.eq_false_iff.mpr old
    constructor
    · intro h
      obtain ⟨im,jm,ij⟩ := (inserted.mp h).resolve_left old
      obtain ⟨ib,jb⟩ := (stay im jm ij no).resolve_left atZ
      exact inserted.mpr (Or.inr ⟨mem_of_mem_erase ib,mem_of_mem_erase jb,ij⟩)
    · intro h
      obtain ⟨ib,jb,ij⟩ := (inserted.mp h).resolve_left old
      obtain ⟨im,jm⟩ := (back ib jb ij no).resolve_left atA
      exact inserted.mpr (Or.inr ⟨im,jm,ij⟩)

/-- Four actual labels suffice for a decrease of the terminal value.
No quantitative size of the strict price difference is required. -/
theorem cheaper_square {q n} (X : Model q n) (hq : 2≤q) {F B} (step : Boundary X F B)
    {p : ℕ→ℚ} {c : ℚ} (cols : ∀v∈X.V,WeightedSD.col q (graph X.D (insert B F)) X.V p v=c)
    {r a b z} (rb : r∈B) (ab : a∈B) (bb : b∈B) (zv : z∈X.V) (outside : z∉B)
    (ra : graph X.D F r a=true) (rz : graph X.D F r z=true)
    (ed : X.D a b=true) (zb : X.D z b=true) (offA : graph X.D F a b=false) (offZ : graph X.D F z b=false)
    (discount : p z<p a) : Cheaper X F B p c := by
  classical
  have cb : Cycle X.D X.V q B := (mem_filter.mp step.1).2
  obtain ⟨comp,same,replace⟩ := square X hq step rb ab bb zv outside ra rz ed zb offA offZ
  exact cheaper_of_swap X (by omega) comp (congrArg card same) cols (cb.sub ab) (cb.sub bb) zv
    (inserted.mpr (Or.inr ⟨ab,bb,ed⟩)) (fun h => by
      rcases inserted.mp h with old|inB
      · exact Bool.noConfusion (offZ.symm.trans old)
      · exact outside inB.1) replace discount

theorem terminal_floor {q n} (X : Model q n) (hq : 2≤q) {F B} (step : Boundary X F B)
    {p : ℕ→ℚ} {c : ℚ} (cols : ∀v∈X.V,WeightedSD.col q (graph X.D (insert B F)) X.V p v=c)
    (stuck : ¬Cheaper X F B p c)
    {r a b z} (rb : r∈B) (ab : a∈B) (bb : b∈B) (zv : z∈X.V) (outside : z∉B)
    (ra : graph X.D F r a=true) (rz : graph X.D F r z=true) (ed : X.D a b=true) (zb : X.D z b=true)
    (offA : graph X.D F a b=false) (offZ : graph X.D F z b=false) : p a≤p z := by
  by_contra! cheaper
  exact stuck (cheaper_square X hq step cols rb ab bb zv outside ra rz ed zb offA offZ cheaper)

#print axioms terminal_floor

#print axioms square
#print axioms cheaper_square
end LeanCH.BR.Closure.SharedArcTailExchange
