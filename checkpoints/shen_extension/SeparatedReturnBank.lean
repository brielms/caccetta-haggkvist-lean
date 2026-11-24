import checkpoints.shen_extension.CommonExitReplacement

namespace LeanCH.BR.Closure.SeparatedReturnBank
open Finset BRq2 BRq3 DeficitLevels

def hub (D : CH.Digraph) (z : ℕ) (I H : Finset ℕ) : CH.Digraph := fun x y =>
  if x=z then decide (y∈H) else if y=z then decide (x∈I) else D x y

/-- Inside W, a path either uses only original arcs or has an original
prefix ending at an entry row before its first visit to the hub. -/
private theorem first_entry {D W z I H x y n} (fresh : z∉W)
    (walk : Walk (hub D z I H) (insert z W) x y n) (xw : x∈W) :
    Walk D W x y n ∨ ∃a∈I, ∃k<n, Walk D W x a k := by
  induction walk with
  | refl => exact Or.inl (.refl _)
  | @step x b y n bu arc tail ih =>
    have xz : x≠z := fun eq => fresh (eq ▸ xw)
    rcases mem_insert.mp bu with rfl|bw
    · exact Or.inr ⟨x,by simpa [hub,xz] using arc,0,by omega,.refl _⟩
    · have bz : b≠z := fun eq => fresh (eq ▸ bw)
      have xb : D x b=true := by simpa [hub,xz,bz] using arc
      rcases ih bw with old|⟨a,ai,k,lt,pre⟩
      · exact Or.inl (.step bw xb old)
      · exact Or.inr ⟨a,ai,k+1,by omega,.step bw xb pre⟩

theorem hub_safe {D W q z I H} (free : QFree D W q) (fresh : z∉W) (hw : H⊆W)
    (far : ∀h∈H, ∀i∈I, ∀k, k+2≤q → ¬Walk D W h i k) :
    QFree (hub D z I H) (insert z W) q := by
  have atHub (n) (pos : 1≤n) (le : n≤q) (w : Walk (hub D z I H) (insert z W) z z n) : False := by
    cases w with
    | refl => omega
    | @step _ b _ k bu edge tail =>
      have bh : b∈H := by simpa [hub] using edge
      rcases first_entry fresh tail (hw bh) with old|⟨i,hi,k',lt,pre⟩
      · rcases old.end_mem_or with eq|zw
        · exact fresh (eq.symm ▸ hw bh)
        · exact fresh zw
      · exact far b bh i hi k' (by omega) pre
  intro x n pos le w
  rcases DeleteRepair.split_or_avoid {z} w with old|⟨a,az,i,j,_,eq,pre,post⟩
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    obtain ⟨_,_,xw,_⟩ := old.unsnoc
    have sub : insert z W \ {z}⊆W := by
      intro b hb
      exact (mem_insert.mp (mem_sdiff.mp hb).1).resolve_left (fun e => (mem_sdiff.mp hb).2 (mem_singleton.mpr e))
    have move {a b j} (v : Walk (hub D z I H) (insert z W \ {z}) a b j)
        (av : a∈W) : Walk D W a b j := by
      induction v with
      | refl => exact .refl _
      | @step a b _ _ bw edge _ ih =>
        have aw : a≠z := fun e => fresh (e ▸ av)
        have bz : b≠z := fun e => fresh (e ▸ sub bw)
        exact .step (sub bw) (by simpa [hub,aw,bz] using edge) (ih (sub bw))
    exact free x _ pos le (move old (sub xw))
  · have eqz : a=z := mem_singleton.mp az
    subst a
    exact atHub (j+i) (by omega) (by omega) (post.append pre)

/-- A finite cut supplies negative incidences. No positive common-exit
rectangle is required: the internal circulant can use every retained exit
with no short retained return to any row needing the bank. -/
theorem funded {D : CH.Digraph} {W I H : Finset ℕ} {q d m : ℕ} (free : QFree D W q) (hq : 1≤q) (hw : H⊆W)
    (far : ∀h∈H, ∀i∈I, ∀k, k+2≤q → ¬Walk D W h i k)
    (room : q*(d-H.card)<m)
    (paid : ∀x∈W, d≤(outN D W x).card+(if x∈I then m else 0)) :
    ∃ E U, U.Nonempty ∧ U.card=W.card+m ∧ QFree E U q ∧ ∀x∈U,d≤(outN E U x).card := by
  classical
  let z := W.sup id + 1
  have fresh : z∉W := by
    intro hz
    have bound : z≤W.sup id := le_sup (f:=id) hz
    dsimp [z] at bound
    omega
  let F := hub D z I H
  have safe := hub_safe free fresh hw far
  have xz (x) (hx : x∈W) : x≠z := fun e => fresh (e ▸ hx)
  have exits (a) (ha : a∈({z}:Finset ℕ)) (h) (hh : h∈H) : F a h=true := by
    have az := mem_singleton.mp ha
    simp [F,hub,az,hh]
  have pay (x) (hx : x∈W) : d≤(outN F W x).card+(if (outN F {z} x).Nonempty then m else 0) := by
    have eq : outN F W x=outN D W x := by
      ext b
      simp only [mem_outN]
      exact and_congr_right (fun bw => by simp [F,hub,xz x hx,xz b bw])
    have iff : (outN F {z} x).Nonempty ↔ x∈I := by
      constructor
      · rintro ⟨a,ha⟩
        obtain ⟨az,xa⟩ := mem_outN.mp ha
        simpa [F,hub,xz x hx,mem_singleton.mp az] using xa
      · intro hi
        exact ⟨z,mem_outN.mpr ⟨mem_singleton_self _,by simp [F,hub,xz x hx,hi]⟩⟩
    simpa only [eq,iff] using (show d≤(outN D W x).card+(if x∈I then m else 0) from paid x hx)
  exact CommonExitReplacement.funded safe hq (singleton_subset_iff.mpr (mem_insert_self _ _))
    (subset_insert _ _) hw exits room pay

#print axioms hub_safe
#print axioms funded
end LeanCH.BR.Closure.SeparatedReturnBank
