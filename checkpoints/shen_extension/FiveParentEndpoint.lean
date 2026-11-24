import checkpoints.shen_extension.FiveParentPayment
import LeanCH.BR.BRNearBoundaryRows
import LeanCH.BR.BRWeightedPressureFrontier
import LeanCH.BR.Triangle24

namespace LeanCH.BR.ShenPuncture.FiveParent
open BRq2 BRq3 Finset

private theorem tri {D W a b c} (free : QFree D W 3) (ha : a∈W) (hb : b∈W) (hc : c∈W)
    (ab : D a b=true) (bc : D b c=true) : D c a≠true := fun ca =>
  free a 3 (by decide) le_rfl (.step hb ab (.step hc bc (.step ha ca (.refl a))))

theorem five_dominating_false {D : CH.Digraph} {W H : Finset ℕ} {d : ℕ}
    (free : QFree D W 3) (hd : 2≤d) (size : W.card=3*d+1)
    (law : BankLaw d) (lower : BankLaw (d-1))
    (hh : H⊆W) (five : H.card=5)
    (counts : ∀ z∈W, (outN D W z).card=if z∈H then d else d+1)
    (dom : ∀ z∈W, ∃ p∈H, D p z=true) : False := by
  classical
  let K := W \ H
  have ksize := card_sdiff_add_card_eq_card hh
  change K.card+H.card=W.card at ksize
  have kpos : K.Nonempty := card_pos.mp (by omega)
  have deg (z) (hz : z∈W) : d≤(outN D W z).card := by rw [counts z hz]; split <;> omega
  have tight {z} (hz : z∈W) (eq : (outN D W z).card=d) : z∈H := by
    by_contra miss; simp [counts z hz,miss] at eq
  obtain ⟨y,yk,large⟩ : ∃ y∈K, 3≤(H ∩ outN D W y).card := by
    by_contra! small
    apply (bankLaw_iff _).mp lower D K (free.mono_set sdiff_subset) kpos (by omega)
    intro z zk
    have row : outN D K z=outN D W z \ H := by ext j; simp only [K,mem_outN,mem_sdiff]; tauto
    have sum := card_sdiff_add_card_inter (outN D W z) H
    rw [inter_comm] at sum
    have full := counts z (mem_sdiff.mp zk).1
    simp [(mem_sdiff.mp zk).2] at full
    rw [row]; have := small z zk; omega
  let S := H ∩ outN D W y
  have sH : S⊆H := inter_subset_left
  have yW := (mem_sdiff.mp yk).1
  have ysize : (outN D W y).card=d+1 := by simpa [(mem_sdiff.mp yk).2] using counts y yW
  obtain ⟨a,ah,ay⟩ := dom y yW
  obtain ⟨q,qh,qa⟩ := dom a (hh ah)
  have aW := hh ah
  have qW := hh qh
  have aq : a≠q := fun e => loopfree free (by decide) qW (e ▸ qa)
  have absentA := digonfree free (by decide) aW yW ay
  have absentQ := tri free qW aW yW qa ay
  have complement : H \ S = {a,q} := by
    symm
    apply eq_of_subset_of_card_le
    · apply insert_subset (mem_sdiff.mpr ⟨ah,fun h => absentA (mem_outN.mp (mem_inter.mp h).2).2⟩)
      exact singleton_subset_iff.mpr (mem_sdiff.mpr ⟨qh,fun h => absentQ (mem_outN.mp (mem_inter.mp h).2).2⟩)
    · have sum := card_sdiff_add_card_eq_card sH
      rw [card_pair aq]
      change 3≤S.card at large
      omega
  have cardS : S.card=3 := by
    have sum := card_sdiff_add_card_eq_card sH
    rw [complement,card_pair aq] at sum; omega
  have classify {z} (hz : z∈H) (no : D y z≠true) : z=a ∨ z=q := by
    have hit : z∈H \ S := mem_sdiff.mpr ⟨hz,fun e => no (mem_outN.mp (mem_inter.mp e).2).2⟩
    simpa [complement] using hit
  have pA {z} (hz : z∈H) (za : D z a=true) : z=q :=
    (classify hz (tri free (hh hz) aW yW za ay)).resolve_left
      (fun eq => loopfree free (by decide) aW (eq ▸ za))
  have pY {z} (hz : z∈H) (zy : D z y=true) : z=a := by
    by_contra ne
    have zq := (classify hz (digonfree free (by decide) (hh hz) yW zy)).resolve_left ne
    subst z
    obtain ⟨p,ph,pq⟩ := dom q qW
    rcases classify ph (tri free (hh ph) qW yW pq zy) with rfl|rfl
    · exact digonfree free (by decide) qW (hh ph) qa pq
    · exact loopfree free (by decide) qW pq
  let Z := outN D W y \ outN D W a
  have exceptional {z} (hit : z∈Z) : z∈S ∧ D z q=true := by
    obtain ⟨zy,miss⟩ := mem_sdiff.mp hit
    have zW := outN_subset zy
    have fails := fun room => miss (mem_outN.mpr ⟨zW,must_share free size.le law deg yW aW zW ay
      (mem_outN.mp zy).2 (fun _ h e => pY (tight h e)) (fun _ h e => pA (tight h e)) room⟩)
    have low : ¬d<(outN D W z).card := fun high => fails (.inl high)
    exact ⟨mem_inter.mpr ⟨tight zW (le_antisymm (by omega) (deg _ zW)),zy⟩,
      by by_contra no; exact fails (.inr no)⟩
  have zs : Z⊆S := fun _ h => (exceptional h).1
  have asize : (outN D W a).card=d := by simp [counts a aW,ah]
  have two : 2≤Z.card := by
    let shared := outN D W y ∩ outN D W a
    have hit : insert y shared ⊆ outN D W a := insert_subset (mem_outN.mpr ⟨yW,ay⟩) inter_subset_right
    have fresh : y∉shared := fun e => loopfree free (by decide) yW (mem_outN.mp (mem_inter.mp e).1).2
    have le := card_le_card hit
    rw [card_insert_of_notMem fresh,asize] at le
    have sum := card_sdiff_add_card_inter (outN D W y) (outN D W a)
    change Z.card+shared.card=(outN D W y).card at sum
    omega
  obtain ⟨w,ws,source⟩ := exists_sink ((free.reverse).mono_set (sH.trans hh))
    (card_pos.mp (by omega : 0<S.card)) cardS.le
  have wW := hh (sH ws)
  have yw := (mem_outN.mp (mem_inter.mp ws).2).2
  have outsideZ : w∉Z := by
    intro wz
    obtain ⟨p,ph,pw⟩ := dom w wW
    by_cases ps : p∈S
    · exact source _ ps pw
    have nyp : D y p≠true := fun e => ps (mem_inter.mpr ⟨ph,mem_outN.mpr ⟨hh ph,e⟩⟩)
    rcases classify ph nyp with rfl|rfl
    · exact (mem_sdiff.mp wz).2 (mem_outN.mpr ⟨wW,pw⟩)
    · exact digonfree free (by decide) wW qW (exceptional wz).2 pw
  have splitS : S=insert w Z := by
    symm
    apply eq_of_subset_of_card_le (insert_subset ws zs)
    rw [card_insert_of_notMem outsideZ]; omega
  have cz : Z.card=2 := by rw [splitS,card_insert_of_notMem outsideZ] at cardS; omega
  obtain ⟨u,v,uv,Zeq⟩ := card_eq_two.mp cz
  have uz : u∈Z := by simp [Zeq]
  have vz : v∈Z := by simp [Zeq]
  have us := zs uz
  have vs := zs vz
  have uW := hh (sH us)
  have vW := hh (sH vs)
  have uq := (exceptional uz).2
  have vq := (exceptional vz).2
  have aw : D a w=true := by
    by_contra no; exact outsideZ (mem_sdiff.mpr ⟨(mem_inter.mp ws).2,fun h => no (mem_outN.mp h).2⟩)
  have labels {p} (ph : p∈H) : p=q ∨ p=a ∨ p=w ∨ p=u ∨ p=v := by
    by_cases e : D y p=true
    · have ps : p∈S := mem_inter.mpr ⟨ph,mem_outN.mpr ⟨hh ph,e⟩⟩
      simp only [splitS,Zeq,mem_insert,mem_singleton] at ps; tauto
    · have := classify ph e; tauto
  have pQ {p} (ph : p∈H) (pq : D p q=true) : p=u ∨ p=v := by
    rcases labels ph with rfl|rfl|rfl|rfl|rfl
    · exact (loopfree free (by decide) qW pq).elim
    · exact (digonfree free (by decide) qW aW qa pq).elim
    · exact (tri free qW aW wW qa aw pq).elim
    all_goals simp
  have notQW : D q w≠true := by
    obtain ⟨b,bz,bsrc⟩ := exists_sink ((free.reverse).mono_set (zs.trans (sH.trans hh)))
      ⟨u,uz⟩ (by omega : Z.card≤3)
    obtain ⟨p,ph,pb⟩ := dom b (hh (sH (zs bz)))
    have pw : p=w := by
      rcases labels ph with rfl|rfl|e|rfl|rfl
      · exact (digonfree free (by decide) (hh (sH (zs bz))) qW (exceptional bz).2 pb).elim
      · exact ((mem_sdiff.mp bz).2 (mem_outN.mpr ⟨hh (sH (zs bz)),pb⟩)).elim
      · exact e
      · exact (bsrc _ uz pb).elim
      · exact (bsrc _ vz pb).elim
    exact tri free wW (hh (sH (zs bz))) qW (pw ▸ pb) (exceptional bz).2
  have pW {z} (zh : z∈H) (zw : D z w=true) : z=a := by
    rcases labels zh with rfl|eq|rfl|rfl|rfl
    · exact (notQW zw).elim
    · exact eq
    · exact (source _ ws zw).elim
    · exact (source _ us zw).elim
    · exact (source _ vs zw).elim
  have headsA : outN D W a⊆insert y (outN D W y) := by
    let shared := outN D W y ∩ outN D W a
    have fresh : y∉shared := fun h => loopfree free (by decide) yW (mem_outN.mp (mem_inter.mp h).1).2
    have eq : insert y shared=outN D W a := by
      apply eq_of_subset_of_card_le (insert_subset (mem_outN.mpr ⟨yW,ay⟩) inter_subset_right)
      have sum := card_sdiff_add_card_inter (outN D W y) (outN D W a)
      change Z.card+shared.card=(outN D W y).card at sum
      rw [card_insert_of_notMem fresh,asize]; omega
    exact eq ▸ insert_subset_insert _ inter_subset_left
  have nested := nested_rows free size.le law deg aW yW (mem_inter.mp ws).2 aw
    (by simp [counts w wW,sH ws]) ysize
    (fun _ h e => pW (tight h e)) (fun _ h e => pA (tight h e)) headsA
    (by
      intro p hp e pq
      rcases pQ (tight hp e) pq with rfl|rfl
      · exact (mem_inter.mp us).2
      · exact (mem_inter.mp vs).2)
  have yu := (mem_outN.mp (mem_inter.mp us).2).2
  have yv := (mem_outN.mp (mem_inter.mp vs).2).2
  have wu : D w u=true := (mem_outN.mp (show u∈outN D W w from nested ▸
    mem_erase.mpr ⟨fun eq => outsideZ (eq ▸ uz),(mem_inter.mp us).2⟩)).2
  have wv : D w v=true := (mem_outN.mp (show v∈outN D W w from nested ▸
    mem_erase.mpr ⟨fun eq => outsideZ (eq ▸ vz),(mem_inter.mp vs).2⟩)).2
  let F := ((outN D W a).erase y).erase w
  have wy : w≠y := fun eq => (mem_sdiff.mp yk).2 (eq ▸ sH ws)
  have wKeep : w∈(outN D W a).erase y := mem_erase.mpr ⟨wy,mem_outN.mpr ⟨wW,aw⟩⟩
  have fsize : F.card+2=d := by
    dsimp only [F]
    rw [card_erase_of_mem wKeep,card_erase_of_mem (mem_outN.mpr ⟨yW,ay⟩),asize]
    omega
  have gc {p} (ph : p∈H) : (outN D W p).card=d := by simp [counts p (hh ph),ph]
  have au : D a u≠true := fun e => (mem_sdiff.mp uz).2 (mem_outN.mpr ⟨uW,e⟩)
  have av : D a v≠true := fun e => (mem_sdiff.mp vz).2 (mem_outN.mpr ⟨vW,e⟩)
  have frows {f} (fin : f∈F) :
      f∈outN D W a ∧ f∈outN D W w ∧ f∈outN D W u ∧ f∈outN D W v := by
    have fw := (mem_erase.mp fin).1
    have fy := (mem_erase.mp (mem_of_mem_erase fin)).1
    have af := mem_of_mem_erase (mem_of_mem_erase fin)
    have fW := outN_subset af
    have yf := (mem_insert.mp (headsA af)).resolve_left fy
    have wf : f∈outN D W w := nested ▸ mem_erase.mpr ⟨fw,yf⟩
    have outH : f∉H := by
      intro h
      rcases labels h with rfl|rfl|rfl|rfl|rfl
      · exact digonfree free (by decide) qW aW qa (mem_outN.mp af).2
      · exact loopfree free (by decide) aW (mem_outN.mp af).2
      · exact fw rfl
      · exact au (mem_outN.mp af).2
      · exact av (mem_outN.mp af).2
    have rich : d<(outN D W f).card := by simp [counts f fW,outH]
    obtain ⟨uf,vf⟩ := both_feed free size.le law deg aW uW vW qW fW yW ay yu yv
      (mem_outN.mp yf).2 (mem_outN.mp af).2 uq vq rich (gc (sH us)) (gc (sH vs)) au av
      (fun _ h e => pY (tight h e)) (fun _ h e => pA (tight h e)) (by
        intro z hz eq fz
        rcases labels (tight hz eq) with rfl|rfl|rfl|eq|eq
        · exact (tri free qW aW fW qa (mem_outN.mp af).2 fz).elim
        · exact (digonfree free (by decide) aW fW (mem_outN.mp af).2 fz).elim
        · exact (digonfree free (by decide) wW fW (mem_outN.mp wf).2 fz).elim
        · exact .inl eq
        · exact .inr eq)
    exact ⟨af,wf,mem_outN.mpr ⟨fW,uf⟩,mem_outN.mpr ⟨fW,vf⟩⟩
  let rem := fun p => outN D W p \ F
  have rc {p} (ph : p∈H) (sub : F⊆outN D W p) : (rem p).card=2 := by
    have := card_sdiff_add_card_eq_card sub
    change (rem p).card+F.card=(outN D W p).card at this
    rw [gc ph] at this
    omega
  have ra := rc ah (fun _ h => (frows h).1)
  have rw' := rc (sH ws) (fun _ h => (frows h).2.1)
  have ru := rc (sH us) (fun _ h => (frows h).2.2.1)
  have rv := rc (sH vs) (fun _ h => (frows h).2.2.2)
  have qout : q∉F := fun h => digonfree free (by decide) qW aW qa (mem_outN.mp (frows h).1).2
  have qboth : q∈rem u ∩ rem v := mem_inter.mpr ⟨mem_sdiff.mpr ⟨mem_outN.mpr ⟨qW,uq⟩,qout⟩,
    mem_sdiff.mpr ⟨mem_outN.mpr ⟨qW,vq⟩,qout⟩⟩
  have charge := card_union_add_card_inter (rem u) (rem v)
  have nonzero := card_pos.mpr ⟨q,qboth⟩
  have cov : W ⊆ ((outN D W q ∪ F) ∪ (rem a ∪ rem w)) ∪ (rem u ∪ rem v) := by
    intro j hj
    by_cases hit : j∈F
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _ hit))
    obtain ⟨p,ph,pj⟩ := dom j hj
    have arc := mem_outN.mpr ⟨hj,pj⟩
    have rr : j∈rem p := mem_sdiff.mpr ⟨arc,hit⟩
    rcases labels ph with rfl|rfl|rfl|rfl|rfl
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ arc))
    · exact mem_union_left _ (mem_union_right _ (mem_union_left _ rr))
    · exact mem_union_left _ (mem_union_right _ (mem_union_right _ rr))
    · exact mem_union_right _ (mem_union_left _ rr)
    · exact mem_union_right _ (mem_union_right _ rr)
  have total := (card_le_card cov).trans (card_union_le _ _)
  have leftCap := card_union_le (outN D W q ∪ F) (rem a ∪ rem w)
  have qf := card_union_le (outN D W q) F
  have awCap := card_union_le (rem a) (rem w)
  have qsize := gc qh
  have smallDegree : d≤4 := by omega
  exact WeightedSD.boundary_regular_no_excess (by decide : 1≤3)
    (Triangle24.br_le_seven (by omega) (by omega)) free size deg yW (by omega)

#print axioms five_dominating_false

/-- Direct entry from the capstone's terminal puncture. No intermediate
promotion, switch, five-role diagram or row equality is assumed. -/
theorem native_endpoint_false {E U A s n t} (h : PunctureAt E U A s n) (hn : n≤3*s)
    (hs : 3≤s) (stop : Blocked E U s) (lower : ∀ j<s, BankLaw j)
    (one : tight E U s={t}) (endpoint : (available E U s).card+7=3*s) :
    False := by
  let H := payingParents E U s
  let W := U.erase t
  have top := (single_tight_window h hn hs stop lower one).1
  have ht : t∈tight E U s := by simp [one]
  have tu := (mem_filter.mp ht).1
  have sizeW : W.card=3*(s-1)+1 := by
    have ord := h.size
    change (U.erase t).card=_
    rw [card_erase_of_mem tu]; omega
  have disj : Disjoint (tight E U s) (available E U s) :=
    disjoint_left.mpr (fun _ hit hk => (mem_filter.mp hk).2.1 hit)
  have tk : tight E U s ∪ available E U s ⊆ U := union_subset (filter_subset _ _) (filter_subset _ _)
  have part := card_sdiff_add_card_eq_card tk
  change H.card+(tight E U s ∪ available E U s).card=U.card at part
  rw [card_union_of_disjoint disj,one,card_singleton] at part
  have five : H.card=5 := by have := h.size; omega
  have sub : H⊆W := fun z hz => mem_erase.mpr
    ⟨fun eq => (mem_sdiff.mp hz).2 (mem_union_left _ (eq ▸ ht)),(mem_sdiff.mp hz).1⟩
  apply five_dominating_false (h.free.mono_set (erase_subset _ _)) (by omega) sizeW
    (lower _ (by omega)) (lower _ (by omega)) sub five
  · intro z zw
    obtain ⟨zt,zu⟩ := mem_erase.mp zw
    have nt : z∉tight E U s := by simpa only [one,mem_singleton] using zt
    have full := (h.degrees z zu).resolve_left (fun eq => nt (mem_filter.mpr ⟨zu,eq⟩))
    have charP : z∈H ↔ E z t=true := by
      constructor
      · intro zh
        by_contra miss
        apply (mem_sdiff.mp zh).2 (mem_union_right _ (mem_filter.mpr ⟨zu,nt,?_⟩))
        rw [one]
        exact disjoint_left.mpr (fun j hj jt => miss ((mem_singleton.mp jt) ▸ (mem_outN.mp hj).2))
      · intro hit
        refine mem_sdiff.mpr ⟨zu,fun bad => ?_⟩
        rcases mem_union.mp bad with m|k
        · exact nt m
        · exact disjoint_left.mp (mem_filter.mp k).2.2 (mem_outN.mpr ⟨tu,hit⟩) ht
    have row : outN E W z=(outN E U z).erase t := by
      ext j; simp only [W,mem_erase,mem_outN]; tauto
    rw [row]
    by_cases zh : z∈H
    · simp only [zh,ite_true,card_erase_of_mem (mem_outN.mpr ⟨tu,charP.mp zh⟩),full]
    · have absent : t∉outN E U z := fun hit => zh (charP.mpr (mem_outN.mp hit).2)
      simp only [zh,ite_false,erase_eq_of_notMem absent,full]; omega
  · intro z zw
    obtain ⟨zt,zu⟩ := mem_erase.mp zw
    obtain ⟨p,ph,_,pz⟩ := single_tight_common_parent h hn hs (lower _ (by omega)) one zu zt
    exact ⟨p,ph,pz⟩

#print axioms native_endpoint_false

theorem single_tight_six_parents {E U A s n t} (h : PunctureAt E U A s n) (hn : n≤3*s)
    (hs : 3≤s) (stop : Blocked E U s) (lower : ∀ j<s, BankLaw j) (one : tight E U s={t}) :
    6≤(payingParents E U s).card ∧ (available E U s).card+8≤3*s := by
  have window := single_tight_window h hn hs stop lower one
  have ne := native_endpoint_false h hn hs stop lower one
  have tk : tight E U s ∪ available E U s ⊆ U := union_subset (filter_subset _ _) (filter_subset _ _)
  have disj : Disjoint (tight E U s) (available E U s) :=
    disjoint_left.mpr (fun _ hit hk => (mem_filter.mp hk).2.1 hit)
  have part := card_sdiff_add_card_eq_card tk
  change (payingParents E U s).card+(tight E U s ∪ available E U s).card=U.card at part
  rw [card_union_of_disjoint disj,one,card_singleton] at part
  have ord := h.size
  obtain ⟨top,_,_,cap⟩ := window
  have below : (available E U s).card+7 < 3*s := lt_of_le_of_ne cap ne
  constructor <;> omega

#print axioms single_tight_six_parents

/-- Attach the endpoint conclusion to the same least-degree witness used by
the triangle capstone. The other counts of tight and available rows stay open. -/
theorem least_degree_source {D V s} (free : QFree D V 3) (live : V.Nonempty)
    (order : V.card≤3*s) (degree : ∀ x∈V, s≤(outN D V x).card) :
    ∃ d≤s, (∀ j<d, BankLaw j) ∧ ∃ n≤3*d, ∃ E U A,
      PunctureAt E U A d n ∧ Blocked E U d ∧ (tight E U d).Nonempty ∧
      (∃ v∈tight E U d, 13*d+1≤9*(available E U d).card+15*(missingParents E U d v).card) ∧
      ∀ t, tight E U d={t} → 6≤(payingParents E U d).card ∧ (available E U d).card+8≤3*d := by
  obtain ⟨d,ds,low,n,nd,E,U,A,h,stop,tl,bill⟩ := least_degree_blocked_source free live order degree
  refine ⟨d,ds,low,n,nd,E,U,A,h,stop,tl,bill,?_⟩
  intro t one
  have hd : 3≤d := by
    by_contra! small
    have few := h.few
    rw [one,card_singleton] at few
    have ord := h.size
    have nTop := single_tight_top_order h nd (by omega) (low _ (by omega)) one
    obtain ⟨B,bk,bsize⟩ := exists_subset_card_eq h.available_card
    obtain ⟨G,L,free',live',sz,reg⟩ := restore_source h.free (by omega) h.degrees bk bsize
    obtain ⟨N,subl⟩ := BRsGen35.exists_range L
    have loops : CH.Loopless (BRsGen35.resD G L) N := by
      intro z _
      apply Bool.eq_false_iff.mpr
      intro e
      obtain ⟨hz,_,edge⟩ := BRsGen35.resD_eq.mp e
      exact loopfree free' (by decide) hz edge
    have minSz := ModuleSize.module_size (G:=BRsGen35.resD G L) (by omega : 0<d)
      (Triangle24.br_le_seven (by omega) (by omega)) subl live'.card_pos loops
      (WeightedSD.qfree_restriction_no_short free' N) (by
        intro z hz
        have row : (L.filter (fun j => BRsGen35.resD G L z j=true))=outN G L z := by
          ext j; simp only [mem_filter,mem_outN,BRsGen35.resD_eq]; tauto
        rw [row,reg z hz])
    omega
  exact single_tight_six_parents h nd hd stop low one

#print axioms least_degree_source
end LeanCH.BR.ShenPuncture.FiveParent
