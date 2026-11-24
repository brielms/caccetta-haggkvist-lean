import checkpoints.shen_extension.ContactBallShrink

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- The acyclic claimant on a cycle with one exterior omission gives a
specific exceptional label. Its outgoing arcs stay in the cycle and its
exterior, and all other exterior labels miss it and the whole cycle. -/
theorem guarded_exception {D V q r target C Y} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (room : RoutingRoom q r V.card target)
    (claim : Y∈claims t C) (dag : QFree D (outN D V (t.rep Y)) (outN D V (t.rep Y)).card)
    (size : C.card+1=r) (ew : (exterior D V C).card=r) :
    ∃d∈exterior D V C,Y=C∪{d} ∧ outN D V d⊆C∪exterior D V C ∧
      ∀z∈exterior D V C,z≠d → (∀v∈C,D z v≠true) ∧ D z d≠true := by
  classical
  let u := t.rep Y
  let Z := N3 D V u
  let E := exterior D V C
  let G := C.filter (fun a=>Z⊆outN D V a)
  obtain ⟨key,id⟩ := mem_filter.mp claim
  have hq := room.cycle.1
  have hr := room.growth.2.1
  have fit := room.close
  have space := room.space
  have uv := rep_native t key
  have ey : N2 D V u=Y := rep_key t key
  have rc := t.rooted _ (t.assigned Y key)
  have len := t.length _ (t.assigned Y key)
  rw [id] at rc len
  have data := claim_data free reg (by omega) t key room.cycle dag fit space room.distance room.score
  rw [id] at data
  have chosen := selected_stock free reg (by omega) t key room.cycle dag (by omega) room.distance room.score
  dsimp only at chosen
  rw [id] at chosen
  obtain ⟨_,zw,rows,_⟩ := chosen
  change Z.card+1=r at zw
  change C.card≤G.card+(r-C.card)*(r-q) at rows
  have diff : r-C.card=1 := by omega
  rw [diff,Nat.one_mul] at rows
  have cover : ∀z∈Z,G⊆inN D C z := by
    intro z zm a am
    exact mem_inN.mpr ⟨(mem_filter.mp am).1,(mem_outN.mp ((mem_filter.mp am).2 zm)).2⟩
  obtain equal|⟨d,except,wide|narrow⟩ := data.single
  · have := data.width; rw [equal] at size; omega
  case inr.inr =>
    have := narrow.1; omega
  have yv : Y⊆V := ey ▸ (fun _ h=>N2_subV h)
  have cv := data.inside.trans yv
  have dm : d∈Y\C := except.symm ▸ mem_singleton_self d
  have back : d∈mutualExterior D V C := (mem_union.mp (wide.2 ▸ (mem_sdiff.mp dm).1)).resolve_left (mem_sdiff.mp dm).2
  obtain ⟨de,⟨c,ce⟩⟩ := mem_filter.mp back
  have ds : d∉Z := fun h=>(mem_N3.mp h).2 (mem_N2.mp (ey.symm ▸ (mem_sdiff.mp dm).1)).1
  obtain ⟨a,am⟩ := card_pos.mp (show 0<G.card by omega)
  have zsub : Z⊆E := by
    intro z zm
    have arc := (mem_filter.mp am).2 zm
    exact mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨a,(mem_filter.mp am).1,arc⟩,fun cm=>
      (mem_N3.mp zm).2 (mem_N2.mp (ey.symm ▸ data.inside cm)).1⟩
  have bank : insert d Z=E := eq_of_subset_of_card_le (insert_subset de zsub)
    (by rw [card_insert_of_notMem ds]; change (exterior D V C).card≤Z.card+1; omega)
  have yy : Y=C∪{d} := by
    ext z
    constructor
    · intro zy
      by_cases zc : z∈C
      · exact mem_union_left _ zc
      exact mem_union_right _ (except ▸ (mem_sdiff.mpr ⟨zy,zc⟩ : z∈Y\C))
    · intro zc
      rcases mem_union.mp zc with cc|dd
      · exact data.inside cc
      exact mem_singleton.mp dd ▸ (mem_sdiff.mp dm).1
  have dv := yv (mem_sdiff.mp dm).1
  obtain ⟨f,fc,fd⟩ := mem_biUnion.mp (mem_sdiff.mp de).1
  have path : Walk D V f d 1 := .step dv (mem_outN.mp fd).2 (.refl d)
  have headBound : outN D V d⊆C∪E := by
    intro z edge
    rcases headY (free.mono_bound (by omega : 4≤q)) uv (ey.symm ▸ (mem_sdiff.mp dm).1)
        (outN_subset edge) (mem_outN.mp edge).2 with old|late
    · rcases mem_union.mp old with x|y
      · exact (blocked_after_cycle free (by omega) reg uv dag ((congrArg card ey).trans data.width)
          (data.inside.trans ey.symm.subset) len rc fc (ey.symm ▸ (mem_sdiff.mp dm).1)
          path x (by omega) (by omega) (mem_outN.mp edge).2).elim
      rcases mem_union.mp (yy ▸ (ey ▸ y)) with cc|dd
      · exact mem_union_left _ cc
      exact mem_union_right _ (mem_singleton.mp dd ▸ de)
    · exact mem_union_right _ (zsub late)
  refine ⟨d,de,yy,headBound,?_⟩
  intro z ze neq
  have zm := (mem_insert.mp (bank.symm ▸ (show z∈E from ze))).resolve_left neq
  have many := card_le_card (cover z zm)
  have zv := N3_subV zm
  have repel v (vc : v∈C) l (short : l≤2) (walk : Walk D V z v l) : False := by
    have cap := exception_parents free cv (fun x xm=>((rc x xm).one x xm).ge) zv vc walk (by omega)
    omega
  refine ⟨fun v vc vz=>repel v vc 1 (by decide) (.step (cv vc) vz (.refl v)),?_⟩
  intro zd
  exact repel c (outN_subset ce) 2 (by decide) (.step dv zd (.step (cv (outN_subset ce)) (mem_outN.mp ce).2 (.refl c)))

#print axioms guarded_exception
end LeanCH.BR.LowShellCycleSelection
