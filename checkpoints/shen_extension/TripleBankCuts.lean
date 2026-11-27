import checkpoints.shen_extension.TripleBankMenu
import Mathlib.Combinatorics.Hall.Finite

/-! For fixed common-target menus the remaining cut choices form a 2-CNF
formula. Each old two-step return needs one cut, and no donor can pay two. -/
namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45

/-- Disjoint new heads are already chosen in sufficient quantity on every
short row. Feasibility of the degree floor is equivalent to the clauses on
actual old cuts: at most one per tail, at least one on every return path. -/
theorem fixed_menus_iff {D : CH.Digraph} {V B P : Finset ℕ} {A : ℕ → Finset ℕ} {s : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (sub : B ⊆ V) (pv : P ⊆ V)
    (common : ∀ b ∈ B, P ⊆ outN D V b)
    (menus : ∀ a ∈ V \ B, ∀ z ∈ A a, z ∈ P ∧ 2 ≤ (outN D B a).card ∧ D a z ≠ true)
    (enough : ∀ a ∈ V \ B, (outN D B a).card ≤ (A a).card+1) :
    let U := V \ B
    (∃ C : ℕ → Finset ℕ, QFree (patch D A C) U 3 ∧
      ∀ a ∈ U, s-1 ≤ (outN (patch D A C) U a).card) ↔
    (∃ C : ℕ → Finset ℕ, (∀ a ∈ U, (outN D U a ∩ C a).card ≤ 1) ∧
      ∀ a ∈ U, ∀ z ∈ A a, ∀ w ∈ U, D z w = true → D w a = true → w ∈ C z ∨ a ∈ C w) := by
  classical
  let U := V \ B
  let donor (a : ℕ) := a ∈ P ∨ ∃ z ∈ P, D z a = true
  have inside {z} (zp : z ∈ P) : z ∈ U := mem_sdiff.mpr ⟨pv zp,fun zb =>
    loopfree safe (by decide) (pv zp) (mem_outN.mp (common z zb zp)).2⟩
  have noHits (a) (au : a ∈ U) (da : donor a) : outN D B a = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro b ed
    obtain ⟨bb,ab⟩ := mem_outN.mp ed
    rcases da with ap | ⟨z,zp,za⟩
    · exact digonfree safe (by decide) (sub bb) (pv ap) (mem_outN.mp (common b bb ap)).2 ab
    · exact safe b 3 (by decide) (by decide) (.step (pv zp) (mem_outN.mp (common b bb zp)).2
        (.step (mem_sdiff.mp au).1 za (.step (sub bb) ab (.refl _))))
  have split (a) (au : a ∈ U) : (outN D U a).card + (outN D B a).card = s := by
    have h := card_outN_union (D := D) (show Disjoint B U from disjoint_sdiff) a
    rw [union_sdiff_of_subset sub,reg a (mem_sdiff.mp au).1] at h
    omega
  have emptyMenu (a) (au : a ∈ U) (da : donor a) : A a = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z za
    have paid := (menus a au z za).2.1
    simp [noHits a au da] at paid
  have clean {a z} (au : a ∈ U) (za : z ∈ A a) :
      z ∈ U ∧ z ≠ a ∧ D a z ≠ true ∧ D z a ≠ true := by
    obtain ⟨zp,two,fresh⟩ := menus a au z za
    obtain ⟨b,ed⟩ := card_pos.mp (show 0 < (outN D B a).card by omega)
    obtain ⟨bb,ab⟩ := mem_outN.mp ed
    have bz := (mem_outN.mp (common b bb zp)).2
    have av := (mem_sdiff.mp au).1
    exact ⟨inside zp,fun eq => digonfree safe (by decide) (sub bb) av (eq ▸ bz) ab,fresh,
      fun back => safe a 3 (by decide) (by decide) (.step (sub bb) ab (.step (pv zp) bz (.step av back (.refl _))))⟩
  constructor
  · rintro ⟨C,ok,floor⟩
    let K (a : ℕ) := if donor a then C a else ∅
    refine ⟨K,?_,?_⟩
    · intro a au
      by_cases da : donor a
      · have old := split a au
        rw [noHits a au da,card_empty,add_zero] at old
        have eq : outN (patch D A C) U a = outN D U a \ C a := by
          ext w; simp [patch,mem_outN,emptyMenu a au da,and_assoc]
        have paid := floor a au
        change s-1 ≤ (outN (patch D A C) U a).card at paid
        rw [eq] at paid
        have count := card_sdiff_add_card_inter (outN D U a) (C a)
        change (outN D U a ∩ K a).card ≤ 1
        rw [show K a = C a by simp [K,da]]
        omega
      · simp [K,da]
    · intro a au z za w wu zw wa
      have zp := (menus a au z za).1
      have dz : donor z := Or.inl zp
      have dw : donor w := Or.inr ⟨z,zp,zw⟩
      by_contra! missed
      have kz : w ∉ C z := by simpa [K,dz] using missed.1
      have kw : a ∉ C w := by simpa [K,dw] using missed.2
      have new : patch D A C a z = true := decide_eq_true (Or.inl za)
      have first : patch D A C z w = true := decide_eq_true (Or.inr ⟨zw,kz⟩)
      have second : patch D A C w a = true := decide_eq_true (Or.inr ⟨wa,kw⟩)
      exact ok a 3 (by decide) (by decide) (.step (inside zp) new (.step wu first (.step au second (.refl _))))
  · rintro ⟨C,cap,returns⟩
    let K (a : ℕ) := if donor a then C a else ∅
    obtain ⟨ok,rows⟩ := patch_certificate (U := U) (A := A) (C := K) (safe.mono_set sdiff_subset)
      (fun _ au _ ed => clean au ed)
      (fun a au z za w wu zw wa => by
        have zp := (menus a au z za).1
        have dz : donor z := Or.inl zp
        have dw : donor w := Or.inr ⟨z,zp,zw⟩
        simpa only [K,ite_eq_left dz,ite_eq_left dw] using returns a au z za w wu zw wa)
      (fun a au z za w wz => by
        have zp := (menus a au z za).1
        rw [emptyMenu z (inside zp) (Or.inl zp)] at wz
        exact False.elim (notMem_empty _ wz))
    refine ⟨K,ok,?_⟩
    intro a au
    rw [rows a au]
    have degree := split a au
    by_cases da : donor a
    · rw [noHits a au da,card_empty,add_zero] at degree
      have count := card_sdiff_add_card_inter (outN D U a) (C a)
      have bound := cap a au
      change (outN D U a ∩ C a).card ≤ 1 at bound
      rw [show K a = C a by simp [K,da]]
      omega
    · rw [show K a = ∅ by simp [K,da],sdiff_empty]
      have room := enough a au
      omega

/-- Rows whose proposed arc to f(c) has an old return through w. -/
def blockers (D : CH.Digraph) (S : Finset ℕ) (f : ℕ → ℕ) (w : ℕ) : Finset ℕ :=
  S.filter (fun c => D (f c) w = true ∧ D w c = true)

def unitAdds (S : Finset ℕ) (f : ℕ → ℕ) (a : ℕ) : Finset ℕ :=
  if a ∈ S then {f a} else ∅

/-- When each short row needs one arc and a blocker serves at most two such
rows, the cut problem is exactly Hall's matching condition on the overloaded
blockers and their proposed targets. This covers arbitrary numbers of rows. -/
theorem hall_cuts_iff {D : CH.Digraph} {V B P S : Finset ℕ} {s : ℕ} {f : ℕ → ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (sub : B ⊆ V) (pv : P ⊆ V)
    (common : ∀ b ∈ B, P ⊆ outN D V b)
    (rows : ∀ c, c ∈ S ↔ c ∈ V \ B ∧ 2 ≤ (outN D B c).card)
    (unit : ∀ a ∈ V \ B, (outN D B a).card ≤ 2)
    (fresh : ∀ c ∈ S, f c ∈ P ∧ D c (f c) ≠ true)
    (load : ∀ w ∈ V \ B, (blockers D S f w).card ≤ 2) :
    let U := V \ B
    let O := U.filter (fun w => 2 ≤ (blockers D S f w).card)
    (∃ C : ℕ → Finset ℕ, QFree (patch D (unitAdds S f) C) U 3 ∧
      ∀ a ∈ U, s-1 ≤ (outN (patch D (unitAdds S f) C) U a).card) ↔
    (∀ X : Finset (↥O), X.card ≤ (X.biUnion (fun w => (blockers D S f w.val).image f)).card) := by
  classical
  let U := V \ B
  let R := blockers D S f
  let O := U.filter (fun w => 2 ≤ (R w).card)
  let A := unitAdds S f
  have add {a z} (ed : z ∈ A a) : a ∈ S ∧ z = f a := by
    by_cases as : a ∈ S
    · exact ⟨as,by simpa [A,unitAdds,as] using ed⟩
    · simp [A,unitAdds,as] at ed
  have present {a} (as : a ∈ S) : f a ∈ A a := by simp [A,unitAdds,as]
  have zu {z} (zp : z ∈ P) : z ∈ U := mem_sdiff.mpr ⟨pv zp,fun zb =>
    loopfree safe (by decide) (pv zp) (mem_outN.mp (common z zb zp)).2⟩
  have spec {w c} (cm : c ∈ R w) : c ∈ S ∧ D (f c) w = true ∧ D w c = true := mem_filter.mp cm
  have rel := fixed_menus_iff (A := A) safe reg sub pv common
    (fun _ _ _ ed => by
      obtain ⟨cs,rfl⟩ := add ed
      exact ⟨(fresh _ cs).1,((rows _).mp cs).2,(fresh _ cs).2⟩)
    (fun a au => by
      by_cases ar : a ∈ S
      · simpa [A,unitAdds,ar] using unit a au
      · have low : (outN D B a).card ≤ 1 := by
          by_contra! many
          exact ar ((rows a).mpr ⟨au,by omega⟩)
        simpa [A,unitAdds,ar] using low)
  dsimp only at rel ⊢
  rw [rel]
  change _ ↔ ∀ X : Finset (↥O), X.card ≤ (X.biUnion (fun w => (R w.val).image f)).card
  rw [all_card_le_biUnion_card_iff_existsInjective']
  constructor
  · rintro ⟨C,budget,cover⟩
    have pick (w : ↥O) : ∃ c ∈ R w.val, w.val ∈ C (f c) := by
      obtain ⟨wu,overload⟩ := mem_filter.mp w.property
      have available : ∃ c ∈ R w.val, c ∉ C w.val := by
        by_contra! allCut
        have incl : R w.val ⊆ outN D U w.val ∩ C w.val := by
          intro c cm
          obtain ⟨cs,_,wc⟩ := spec cm
          exact mem_inter.mpr ⟨mem_outN.mpr ⟨((rows c).mp cs).1,wc⟩,allCut c cm⟩
        have upper := (card_le_card incl).trans (budget w.val wu)
        omega
      obtain ⟨c,cm,nc⟩ := available
      obtain ⟨cs,zw,wc⟩ := spec cm
      exact ⟨c,cm,(cover c ((rows c).mp cs).1 (f c) (present cs) w wu zw wc).resolve_right nc⟩
    choose c cm cut using pick
    refine ⟨fun w => f (c w),?_,fun w => mem_image_of_mem f (cm w)⟩
    intro w v eq
    apply Subtype.ext
    have qp := (fresh _ (spec (cm w)).1).1
    have wmem : w.val ∈ outN D U (f (c w)) ∩ C (f (c w)) :=
      mem_inter.mpr ⟨mem_outN.mpr ⟨(mem_filter.mp w.property).1,(spec (cm w)).2.1⟩,cut w⟩
    have vmem : v.val ∈ outN D U (f (c v)) ∩ C (f (c v)) :=
      mem_inter.mpr ⟨mem_outN.mpr ⟨(mem_filter.mp v.property).1,(spec (cm v)).2.1⟩,cut v⟩
    change f (c w) = f (c v) at eq
    rw [←eq] at vmem
    exact card_le_one.mp (budget _ (zu qp)) _ wmem _ vmem
  · rintro ⟨g,inj,picked⟩
    let e (w : ℕ) := if wo : w ∈ O then g ⟨w,wo⟩ else 0
    let up (a : ℕ) := O.filter (fun w => e w = a)
    let down (w : ℕ) := (R w).filter (fun c => w ∉ O ∨ f c ≠ e w)
    let C (a : ℕ) := if a ∈ P then up a else down a
    have low (w) (wu : w ∈ U) : (down w).card ≤ 1 := by
      by_cases wo : w ∈ O
      · obtain ⟨c,cm,cg⟩ := mem_image.mp (picked ⟨w,wo⟩)
        change c ∈ R w at cm
        have ce : f c = e w := by simpa [e,wo] using cg
        have incl : down w ⊆ (R w).erase c := by
          intro d dm
          obtain ⟨dr,ok⟩ := mem_filter.mp dm
          exact mem_erase.mpr ⟨fun eq => (ok.resolve_left (not_not.mpr wo)) (eq ▸ ce),dr⟩
        have lim := card_le_card incl
        rw [card_erase_of_mem cm] at lim
        have cap := load w wu
        change (R w).card ≤ 2 at cap
        omega
      · have cap : (R w).card ≤ 1 := by
          by_contra! many
          exact wo (mem_filter.mpr ⟨wu,by omega⟩)
        exact (card_le_card (filter_subset _ _)).trans cap
    have high (a) : (up a).card ≤ 1 := by
      apply card_le_one.mpr
      intro w wm v vm
      obtain ⟨wo,we⟩ := mem_filter.mp wm
      obtain ⟨vo,ve⟩ := mem_filter.mp vm
      have ge : g ⟨w,wo⟩ = g ⟨v,vo⟩ := by simpa [e,wo,vo] using (we.trans ve.symm)
      exact congrArg Subtype.val (inj ge)
    refine ⟨C,?_,?_⟩
    · intro a au
      apply (card_le_card inter_subset_right).trans
      by_cases ap : a ∈ P
      · simpa [C,ap] using high a
      · simpa [C,ap] using low a au
    · intro a au z za w wu zw wa
      obtain ⟨as,rfl⟩ := add za
      have zp := (fresh a as).1
      have wb : w ∉ P := by
        intro wp
        obtain ⟨b,ed⟩ := card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) ((rows a).mp as).2)
        obtain ⟨bb,ab⟩ := mem_outN.mp ed
        exact safe a 3 (by decide) (by decide)
          (.step (sub bb) ab (.step (pv wp) (mem_outN.mp (common b bb wp)).2 (.step (mem_sdiff.mp au).1 wa (.refl _))))
      have active : a ∈ R w := mem_filter.mpr ⟨as,zw,wa⟩
      by_cases wo : w ∈ O
      · by_cases we : e w = f a
        · exact Or.inl (by simpa [C,zp,up] using (show w ∈ up (f a) from mem_filter.mpr ⟨wo,we⟩))
        · exact Or.inr (by simpa only [C,ite_eq_right wb] using
            (show a ∈ down w from mem_filter.mpr ⟨active,Or.inr (Ne.symm we)⟩))
      · exact Or.inr (by simpa only [C,ite_eq_right wb] using
          (show a ∈ down w from mem_filter.mpr ⟨active,Or.inl wo⟩))

/-- If every short row on a top-order bank needs only one arc, every
assignment of missing common targets has either a triple collision or a
Hall-deficient set of double blockers. -/
theorem top_cut_obstruction {D : CH.Digraph} {V B P : Finset ℕ} {s : ℕ} {f : ℕ → ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (hs : 2 ≤ s) (order : V.card = 3*s)
    (no : BypassRepair.NoHost 3 (s-1)) (sub : B ⊆ V) (three : B.card = 3)
    (pv : P ⊆ V) (common : ∀ b ∈ B, P ⊆ outN D V b)
    (unit : ∀ c ∈ V \ B, (outN D B c).card ≤ 2)
    (choice : ∀ c ∈ V \ B, 2 ≤ (outN D B c).card → f c ∈ P ∧ D c (f c) ≠ true) :
    let U := V \ B
    let S := U.filter (fun c => 2 ≤ (outN D B c).card)
    let R := blockers D S f
    let O := U.filter (fun w => 2 ≤ (R w).card)
    (∃ w ∈ U, 3 ≤ (R w).card) ∨
      ∃ X : Finset (↥O), (X.biUnion (fun w => (R w.val).image f)).card < X.card := by
  classical
  intro U S R O
  by_cases heavy : ∃ w ∈ U, 3 ≤ (R w).card
  · exact Or.inl heavy
  right
  by_contra! hall
  have size : U.card = 3*(s-1) := by change (V \ B).card = _; rw [card_sdiff_of_subset sub,three,order]; omega
  have load (w) (wu : w ∈ U) : (R w).card ≤ 2 := by
    by_contra! excess
    exact heavy ⟨w,wu,by omega⟩
  have test := hall_cuts_iff (S := S) (f := f) safe reg sub pv common (fun _ => mem_filter)
    unit (fun c cs => choice c (mem_filter.mp cs).1 (mem_filter.mp cs).2) load
  obtain ⟨C,ok,floor⟩ := test.mpr hall
  exact no _ U (card_pos.mp (by omega)) size.le ok floor

#print axioms top_cut_obstruction
#print axioms hall_cuts_iff
#print axioms fixed_menus_iff
end LeanCH.BR.TripleBank

