import checkpoints.shen_extension.ThreeParentOverlap
import checkpoints.shen_extension.GlobalTripleChoice

/-! In the three-tight-parent case, three specified neutral rows have many
common heads in the same exterior set. Compare with the global maximum
over triples of rows before selecting a bank. -/
namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45

/-- Restrict to the one of the two rows that misses the other. Its t-1
heads off c avoid all three labels a,b,c, and are forbidden to L. -/
private theorem exterior_pool {D : CH.Digraph} {U L : Finset ℕ} {a b c d t : ℕ}
    (safe : QFree D U 3) (size : U.card = 3*t) (sat : L.card+1 = t)
    (au : a ∈ U) (bu : b ∈ U) (cu : c ∈ U) (du : d ∈ U)
    (ab : a ≠ b) (ac : D a c = true) (bc : D b c = true)
    (da : (outN D U a).card = t) (db : (outN D U b).card = t)
    (drow : (outN D U d).erase c = L)
    (al : Disjoint (outN D U a) L) (bl : Disjoint (outN D U b) L)
    (avoid : ∀ l ∈ L, D l a ≠ true ∧ D l b ≠ true ∧ D l c ≠ true)
    (gate : ∀ v ∈ (outN D U a ∪ outN D U b).erase c, v ≠ d → D v d = true) :
    ∃ Y : Finset ℕ, Y.card+1 = t ∧ Disjoint L Y ∧ ∀ l ∈ L, outN D U l \ L ⊆ Y := by
  classical
  let T : Finset ℕ := {a,b,c}
  have ncA : a ≠ c := fun e => loopfree safe (by decide) cu (e ▸ ac)
  have ncB : b ≠ c := fun e => loopfree safe (by decide) cu (e ▸ bc)
  have cardT : T.card = 3 := by
    change ({a,b,c} : Finset ℕ).card = 3
    rw [card_insert_of_notMem (by simp [ab,ncA]),card_pair ncB]
  have subT : T ⊆ U := insert_subset au (insert_subset bu (singleton_subset_iff.mpr cu))
  have subL : L ⊆ U := fun _ lm => outN_subset (mem_erase.mp (drow ▸ lm)).2
  have disLT : Disjoint L T := by
    apply disjoint_left.mpr
    intro v vm inside
    rcases mem_insert.mp inside with rfl | rest
    · exact (avoid _ vm).2.2 ac
    rcases mem_insert.mp rest with rfl | ce
    · exact (avoid _ vm).2.2 bc
    · exact (mem_erase.mp (drow ▸ vm)).1 (mem_singleton.mp ce)
  have pick : ∃ F : Finset ℕ, F ⊆ (outN D U a ∪ outN D U b).erase c ∧
      F.card+1=t ∧ Disjoint F L ∧ Disjoint F T := by
    have make {x} (xu : x ∈ U) (xc : D x c = true) (deg : (outN D U x).card = t)
        (side : outN D U x ⊆ outN D U a ∪ outN D U b) (off : Disjoint (outN D U x) L)
        (na : D x a ≠ true) (nb : D x b ≠ true) :
        ∃ F : Finset ℕ, F ⊆ (outN D U a ∪ outN D U b).erase c ∧
          F.card+1=t ∧ Disjoint F L ∧ Disjoint F T := by
      refine ⟨(outN D U x).erase c,fun v h => mem_erase.mpr
        ⟨(mem_erase.mp h).1,side (mem_erase.mp h).2⟩,
        (card_erase_add_one (mem_outN.mpr ⟨cu,xc⟩)).trans deg,off.mono_left (erase_subset _ _),?_⟩
      apply disjoint_left.mpr
      intro v vm vt
      have edge := (mem_outN.mp (mem_erase.mp vm).2).2
      rcases mem_insert.mp vt with rfl | rest
      · exact na edge
      rcases mem_insert.mp rest with rfl | ce
      · exact nb edge
      · exact (mem_erase.mp vm).1 (mem_singleton.mp ce)
    by_cases ed : D a b = true
    · exact make bu bc db subset_union_right bl (digonfree safe (by decide) au bu ed)
        (loopfree safe (by decide) bu)
    · exact make au ac da subset_union_left al (loopfree safe (by decide) au) ed
  obtain ⟨F,fsub,fc,fl,ft⟩ := pick
  have fu : F ⊆ U := fun _ vm => (mem_union.mp (mem_erase.mp (fsub vm)).2).elim
    (fun h => outN_subset h) (fun h => outN_subset h)
  let Z := F ∪ (L ∪ T)
  have cardZ : Z.card = F.card+(L.card+T.card) := by
    change (F ∪ (L ∪ T)).card = _
    rw [card_union_of_disjoint (disjoint_union_right.mpr ⟨fl,ft⟩),card_union_of_disjoint disLT]
  refine ⟨U \ Z,?_,?_,?_⟩
  · have subZ : Z ⊆ U := union_subset fu (union_subset subL subT)
    rw [card_sdiff_of_subset subZ,cardZ]
    omega
  · exact disjoint_left.mpr fun v vl vy => (mem_sdiff.mp vy).2
      (mem_union_right _ (mem_union_left _ vl))
  · intro l lm v vm
    obtain ⟨old,vl⟩ := mem_sdiff.mp vm
    obtain ⟨vu,lv⟩ := mem_outN.mp old
    refine mem_sdiff.mpr ⟨vu,?_⟩
    intro vz
    rcases mem_union.mp vz with vf | rest
    · have dl := (mem_outN.mp (mem_erase.mp (drow ▸ lm)).2).2
      by_cases vd : v = d
      · exact digonfree safe (by decide) du (subL lm) dl (vd ▸ lv)
      · exact safe d 3 (by decide) (by decide) (.step (subL lm) dl (.step vu lv
          (.step du (gate _ (fsub vf) vd) (.refl _))))
    · rcases mem_union.mp rest with vL | vt
      · exact vl vL
      rcases mem_insert.mp vt with rfl | alt
      · exact (avoid _ lm).1 lv
      rcases mem_insert.mp alt with rfl | ce
      · exact (avoid _ lm).2.1 lv
      · exact (avoid _ lm).2.2 (mem_singleton.mp ce ▸ lv)

/-- The three sets can miss at most the sum of their individual omissions. -/
private theorem triple_count {Y A B C : Finset ℕ} (ay : A ⊆ Y) (by' : B ⊆ Y) (cy : C ⊆ Y) :
    A.card+B.card+C.card ≤ ((A∩B)∩C).card+2*Y.card := by
  have h := card_union_add_card_inter A B
  have h' := card_union_add_card_inter (A ∩ B) C
  have h₁ := card_le_card (union_subset ay by')
  have h₂ := card_le_card (union_subset (inter_subset_left.trans ay) cy : (A ∩ B) ∪ C ⊆ Y)
  omega

/-- C is shared by c,d. Two full rows z,k in L, plus any third row in L,
certify a large triple intersection once their exterior support is bounded. -/
private theorem growth_count {D : CH.Digraph} {U C L Y : Finset ℕ} {c d z k t m : ℕ}
    (big : 3 ≤ L.card) (form : L = insert z C) (zk : z ≠ k) (kl : k ∈ L)
    (sizeY : Y.card+1 = t) (outside : ∀ l ∈ L, outN D U l \ L ⊆ Y)
    (shares : C ⊆ outN D U c ∩ outN D U d) (cd : c ≠ d)
    (cu : c ∈ U) (du : d ∈ U) (sub : L ⊆ U)
    (separate : ∀ l ∈ L, l ≠ c ∧ l ≠ d)
    (floor : ∀ l ∈ L, t ≤ (outN D U l).card)
    (zFull : (outN D U z).card = t+1) (kFull : (outN D U k).card = t+1)
    (off : D z z ≠ true)
    (cap : ∀ i ∈ U, ∀ j ∈ U, ∀ h ∈ U, i ≠ j → i ≠ h → j ≠ h →
      ((outN D U i ∩ outN D U j) ∩ outN D U h).card ≤ m) :
    t+2 ≤ 4*m := by
  classical
  let E (l : ℕ) := outN D U l \ L
  let N (l : ℕ) := outN D U l
  have zl : z ∈ L := form ▸ mem_insert_self _ _
  have third : ∃ r ∈ L, r ≠ z ∧ r ≠ k := by
    by_contra! only
    have inc : L ⊆ {z,k} := fun r rl => by
      by_cases rz : r=z
      · simp [rz]
      · simp [only r rl rz]
    have lim := card_le_card inc
    rw [card_pair zk] at lim
    omega
  obtain ⟨r,rl,rz,rk⟩ := third
  have inC (l) (lm : l ∈ L) : (N l ∩ C).card ≤ m := by
    have incl : N l ∩ C ⊆ (N c ∩ N d) ∩ N l := fun _ h =>
      mem_inter.mpr ⟨shares (mem_inter.mp h).2,(mem_inter.mp h).1⟩
    exact (card_le_card incl).trans (cap c cu d du l (sub lm) cd (separate l lm).1.symm (separate l lm).2.symm)
  have parts (l) : (E l).card+(N l ∩ L).card = (N l).card := card_sdiff_add_card_inter _ _
  have upper (l) (lm : l ∈ L) : (N l ∩ L).card ≤ m+1 := by
    have incl : N l ∩ L ⊆ insert z (N l ∩ C) := by
      intro w wm
      obtain ⟨wn,wl⟩ := mem_inter.mp wm
      rcases mem_insert.mp (form ▸ wl) with eq | cm
      · exact mem_insert.mpr (Or.inl eq)
      · exact mem_insert_of_mem (mem_inter.mpr ⟨wn,cm⟩)
    have h := card_le_card incl
    have lim := card_insert_le z (N l ∩ C)
    have exactC := inC l lm
    omega
  have innerZ : N z ∩ L ⊆ N z ∩ C := by
    intro w wm
    obtain ⟨wn,wl⟩ := mem_inter.mp wm
    rcases mem_insert.mp (form ▸ wl) with eq | cm
    · exact False.elim (off (eq ▸ (mem_outN.mp wn).2))
    · exact mem_inter.mpr ⟨wn,cm⟩
  have boundZ := (card_le_card innerZ).trans (inC z zl)
  have triple := triple_count (outside z zl) (outside k kl) (outside r rl)
  change (E z).card+(E k).card+(E r).card ≤ ((E z ∩ E k) ∩ E r).card+2*Y.card at triple
  have incl : (E z ∩ E k) ∩ E r ⊆ (N z ∩ N k) ∩ N r := by
    intro w h
    obtain ⟨zz,rr⟩ := mem_inter.mp h
    obtain ⟨zw,kw⟩ := mem_inter.mp zz
    exact mem_inter.mpr ⟨mem_inter.mpr ⟨(mem_sdiff.mp zw).1,(mem_sdiff.mp kw).1⟩,(mem_sdiff.mp rr).1⟩
  have bounded := (card_le_card incl).trans (cap z (sub zl) k (sub kl) r (sub rl) zk rz.symm rk.symm)
  have dz := parts z
  have dk := parts k
  have dr := parts r
  have ik := upper k kl
  have ir := upper r rl
  have fr := floor r rl
  change (N z).card = t+1 at zFull
  change (N k).card = t+1 at kFull
  change t ≤ (N r).card at fr
  omega

/-- The two disjoint pools supporting all arcs sent by the neutral rows. -/
structure NeutralPools (D : CH.Digraph) (U P : Finset ℕ) (t : ℕ) where
  L : Finset ℕ
  Y : Finset ℕ
  rows : L ⊆ U
  size : L.card+1=t
  equal : Y.card=L.card
  separate : Disjoint L Y
  selected : P ⊆ L
  support : ∀ l ∈ L, outN D U l ⊆ L ∪ Y
  floor : ∀ l ∈ L, t ≤ (outN D U l).card
  full : ∀ p ∈ P, (outN D U p).card=t+1
  internal : ∀ l ∈ L, (outN D U l ∩ L).card ≤ P.card+1

/-- The cardinality compared here is the global maximum on the original
carrier, attained by the bank selected for the repair. -/
theorem bank_menu_pools {D : CH.Digraph} {V B P : Finset ℕ} {s c : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (hs : 8 ≤ s) (order : V.card = 3*s)
    (no : BypassRepair.NoHost 3 (s-1)) (sub : B ⊆ V) (three : B.card = 3)
    (pv : P ⊆ V) (many : 2 ≤ P.card) (common : ∀ b ∈ B, P ⊆ outN D V b)
    (cap : TripleCap D V P.card) (cu : c ∈ V \ B) (hits : (outN D B c).card = 3)
    (lone : ∀ v ∈ V \ B, v ≠ c → (outN D B v).card ≤ 1)
    (menu : (rowMenu D (V \ B) P c).card ≤ 1) (miss : ∃ z ∈ P, D c z ≠ true)
    (eq3 : (tightParents D (V \ B) c (s-1)).card = 3) :
    (s+1 ≤ 4*P.card ∧ 2 ≤ (P ∩ outN D V c).card) ∧ Nonempty (NeutralPools D (V \ B) P (s-1)) := by
  classical
  let t := s-1
  let U := V \ B
  let H := tightParents D U c t
  let C := outN D U c
  have uv : U ⊆ V := sdiff_subset
  have free := safe.mono_set uv
  have size : U.card = 3*t := by
    change (V \ B).card = 3*(s-1)
    rw [card_sdiff_of_subset sub,order,three]; omega
  obtain ⟨z,zp,cz,sat,neutralEq,nb,rest,k,kp,kl,ku,ck,full⟩ :=
    bank_saturation safe reg (by omega) order no sub three pv many common cu hits lone menu miss
  let L := insert z C
  change L.card+1=t at sat
  change neutral D U H c = L at neutralEq
  change k ∈ L at kl
  have clear : L ⊆ neutral D U H c := neutralEq.ge
  have spare (w) (wm : w ∈ outN D U k) : t < (outN D U w).card := by
    rw [full w wm]; dsimp [t]; omega
  obtain ⟨a,b,d,ab,ad,bd,triple,_,_,drow,al,bl,gate⟩ :=
    three_parent_structure free cu ku ck size.le no rest spare sat clear eq3
  change H = {a,b,d} at triple
  have am : a ∈ H := triple ▸ mem_insert_self _ _
  have bm : b ∈ H := triple ▸ mem_insert_of_mem (mem_insert_self _ _)
  have dm : d ∈ H := triple ▸ mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))
  have par {v} (vm : v ∈ H) := mem_inN.mp (mem_filter.mp vm).1
  have nh {v} (vm : v ∈ H) : v ≠ c := fun e => loopfree free (by decide) cu (e ▸ (par vm).2)
  have deg {v} (vm : v ∈ H) : (outN D U v).card = t :=
    le_antisymm (mem_filter.mp vm).2 (rest v (par vm).1 (nh vm))
  have loc {l} (ll : l ∈ L) := mem_erase.mp (mem_sdiff.mp (mem_filter.mp (clear ll)).1).1
  have neutralEdge {l h} (ll : l ∈ L) (hm : h ∈ H) : D l h ≠ true := fun e =>
    disjoint_left.mp (mem_filter.mp (clear ll)).2 (mem_outN.mpr ⟨(par hm).1,e⟩) hm
  obtain ⟨Y,ys,dis,yall⟩ := exterior_pool free size sat (par am).1 (par bm).1 cu (par dm).1 ab
    (par am).2 (par bm).2 (deg am) (deg bm) drow al bl
    (fun l ll => ⟨neutralEdge ll am,neutralEdge ll bm,nb l ll⟩) gate
  have lift {v} : outN D U v ⊆ outN D V v := fun _ h =>
    mem_outN.mpr ⟨uv (outN_subset h),(mem_outN.mp h).2⟩
  have capU (i) (iu : i ∈ U) (j) (ju : j ∈ U) (h) (hu : h ∈ U)
      (ij : i ≠ j) (ih : i ≠ h) (jh : j ≠ h) :
      ((outN D U i ∩ outN D U j) ∩ outN D U h).card ≤ P.card :=
    (card_le_card (inter_subset_inter (inter_subset_inter lift lift) lift)).trans
      (cap i j h (uv iu) (uv ju) (uv hu) ij ih jh)
  have pFull (v) (vp : v ∈ P) : (outN D U v).card = t+1 := by
    have same : outN D U v = outN D V v := by
      ext w
      constructor
      · exact fun m => lift m
      · intro m
        refine mem_outN.mpr ⟨mem_sdiff.mpr ⟨outN_subset m,fun wb =>
          digonfree safe (by decide) (pv vp) (sub wb) (mem_outN.mp m).2
            (mem_outN.mp (common w wb vp)).2⟩,(mem_outN.mp m).2⟩
    rw [same,reg v (pv vp)]; dsimp [t]; omega
  have sh : C ⊆ outN D U c ∩ outN D U d := fun v cm =>
    mem_inter.mpr ⟨cm,(mem_erase.mp (show v ∈ (outN D U d).erase c by rw [drow]; exact mem_insert_of_mem cm)).2⟩
  have zk : z ≠ k := fun e => cz (e ▸ ck)
  have zl : z ∈ L := mem_insert_self _ _
  have len : 3 ≤ L.card := by dsimp [t] at sat; omega
  have grow := growth_count len (rfl : L = insert z C) zk kl ys yall sh (nh dm).symm cu (par dm).1
    (fun _ ll => (loc ll).2) (fun _ ll => ⟨(loc ll).1,fun e => (mem_sdiff.mp (mem_filter.mp
      (clear ll)).1).2 (e ▸ dm)⟩) (fun l ll => rest l (loc ll).2 (loc ll).1)
    (pFull z zp) (pFull k kp) (loopfree free (by decide) (loc zl).2) capU
  have outsideP : P \ outN D V c ⊆ rowMenu D U P c := fun _ wm =>
    mem_union_left _ (mem_sdiff.mpr ⟨(mem_sdiff.mp wm).1,fun hit => (mem_sdiff.mp wm).2 (lift hit)⟩)
  have lim := (card_le_card outsideP).trans menu
  have cnt := card_sdiff_add_card_inter P (outN D V c)
  refine ⟨by dsimp [t] at grow; omega,?_⟩
  have pin (p) (pm : p ∈ P) : p ∈ L := by
    by_cases edge : D c p = true
    · have pb : p ∉ B := fun bm => loopfree safe (by decide) (pv pm)
          (mem_outN.mp (common p bm pm)).2
      exact mem_insert_of_mem (mem_outN.mpr ⟨mem_sdiff.mpr ⟨pv pm,pb⟩,edge⟩)
    · have pmiss : p ∈ P \ outN D V c := mem_sdiff.mpr ⟨pm,fun h => edge (mem_outN.mp h).2⟩
      have zmiss : z ∈ P \ outN D V c := mem_sdiff.mpr ⟨zp,fun h => cz (mem_outN.mp h).2⟩
      exact (card_le_one.mp lim p pmiss z zmiss) ▸ zl
  refine ⟨⟨L,Y,(fun _ ll => (loc ll).2),sat,by omega,dis,(fun _ => pin _),?_,
    (fun l ll => rest l (loc ll).2 (loc ll).1),pFull,?_⟩⟩
  · intro l ll w wm
    by_cases wl : w ∈ L
    · exact mem_union_left _ wl
    · exact mem_union_right _ (yall _ ll (mem_sdiff.mpr ⟨wm,wl⟩))
  · intro l ll
    have ld : l ≠ d := fun e => (mem_sdiff.mp (mem_filter.mp (clear ll)).1).2 (e ▸ dm)
    have hi : (outN D U l ∩ C).card ≤ P.card := by
      refine (card_le_card (show outN D U l ∩ C ⊆ (outN D U c ∩ outN D U d) ∩ outN D U l
        from fun _ m => mem_inter.mpr ⟨sh (mem_inter.mp m).2,(mem_inter.mp m).1⟩)).trans ?_
      exact capU c cu d (par dm).1 l (loc ll).2 (nh dm).symm (loc ll).1.symm ld.symm
    have le := card_le_card (show outN D U l ∩ L ⊆ insert z (outN D U l ∩ C) from by
      intro w wm
      obtain ⟨wn,wl⟩ := mem_inter.mp wm
      rcases mem_insert.mp wl with eq | wc
      · exact mem_insert.mpr (Or.inl eq)
      · exact mem_insert_of_mem (mem_inter.mpr ⟨wn,wc⟩))
    have bound := card_insert_le z (outN D U l ∩ C)
    change (outN D U l ∩ L).card ≤ P.card+1
    omega

theorem bank_menu_growth {D : CH.Digraph} {V B P : Finset ℕ} {s c : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (hs : 8 ≤ s) (order : V.card = 3*s)
    (no : BypassRepair.NoHost 3 (s-1)) (sub : B ⊆ V) (three : B.card = 3)
    (pv : P ⊆ V) (many : 2 ≤ P.card) (common : ∀ b ∈ B, P ⊆ outN D V b)
    (cap : TripleCap D V P.card) (cu : c ∈ V \ B) (hits : (outN D B c).card = 3)
    (lone : ∀ v ∈ V \ B, v ≠ c → (outN D B v).card ≤ 1)
    (menu : (rowMenu D (V \ B) P c).card ≤ 1) (miss : ∃ z ∈ P, D c z ≠ true)
    (eq3 : (tightParents D (V \ B) c (s-1)).card = 3) :
    s+1 ≤ 4*P.card ∧ 2 ≤ (P ∩ outN D V c).card :=
  (bank_menu_pools safe reg hs order no sub three pv many common cap cu hits lone menu miss eq3).1

/-- A globally selected bank at top order carries the increased bound on
its own three-parent alternative, or one of the other live alternatives. -/
theorem selected_growth_frontier {D : CH.Digraph} {V : Finset ℕ} {s : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (hs : 8 ≤ s) (order : V.card = 3*s)
    (no : BypassRepair.NoHost 3 (s-1)) :
    ∃ P ⊆ V, 2 ≤ P.card ∧ TripleCap D V P.card ∧ ∃ B ⊆ V, B.card=3 ∧
      (∀ b ∈ B, P ⊆ outN D V b) ∧
      let U := V \ B
      let S := U.filter (fun c => 2 ≤ (outN D B c).card)
      (∀ c ∈ S, ∃ z ∈ P, D c z ≠ true) ∧
      (2 ≤ S.card ∨ ∃ c, S={c} ∧ (outN D B c).card=3 ∧ (rowMenu D U P c).card=1 ∧
        (4 ≤ (tightParents D U c (s-1)).card ∨
          (tightParents D U c (s-1)).card=3 ∧ s+1 ≤ 4*P.card ∧ 2 ≤ (P ∩ outN D V c).card)) := by
  classical
  obtain ⟨P,pv,many,cap,B,bv,three,common,miss,_,front⟩ :=
    GlobalTripleChoice.top_repair_frontier safe reg (by omega) order no
  refine ⟨P,pv,many,cap,B,bv,three,common,miss,?_⟩
  rcases front with several | ⟨c,one,hits,menu⟩
  · exact Or.inl several
  · refine Or.inr ⟨c,one,hits,menu,?_⟩
    have cs : c ∈ (V \ B).filter (fun a => 2 ≤ (outN D B a).card) := one ▸ mem_singleton_self _
    have lone (v) (vu : v ∈ V \ B) (vc : v ≠ c) : (outN D B v).card ≤ 1 := by
      by_contra! bad
      exact vc (mem_singleton.mp (one ▸ (mem_filter.mpr ⟨vu,by omega⟩)))
    have parents := three_tight_on_lone_frontier safe reg (by omega) order no bv three pv many common
      (mem_filter.mp cs).1 lone menu.le
    by_cases large : 4 ≤ (tightParents D (V \ B) c (s-1)).card
    · exact Or.inl large
    · have eq : (tightParents D (V \ B) c (s-1)).card=3 := by omega
      exact Or.inr ⟨eq,bank_menu_growth safe reg hs order no bv three pv many common cap
        (mem_filter.mp cs).1 hits lone menu.le (miss c cs) eq⟩

#print axioms bank_menu_growth
#print axioms selected_growth_frontier
end LeanCH.BR.TripleBank
