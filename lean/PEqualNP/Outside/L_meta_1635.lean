import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1635

open PEqualNP.CircuitLowerBounds

def Closed {α : Type*} {m : ℕ} (S : Fin m → Finset α) (k : ℕ) (X : Finset α) : Prop :=
  ∀ i : Fin m, i.val < k → ∀ a ∈ S i, ∀ b ∈ S i, (a ∈ X ↔ b ∈ X)

def Together {α : Type*} {m : ℕ} (S : Fin m → Finset α) (k : ℕ) (a b : α) : Prop :=
  ∀ X : Finset α, Closed S k X → (a ∈ X ↔ b ∈ X)

theorem Together.refl {α : Type*} {m : ℕ} (S : Fin m → Finset α) (k : ℕ) (a : α) : Together S k a a :=
  fun _ _ => Iff.rfl

theorem Together.symm {α : Type*} {m : ℕ} {S : Fin m → Finset α} {k : ℕ} {a b : α}
    (h : Together S k a b) : Together S k b a := fun X hX => (h X hX).symm

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_stepW_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepW]; omega

theorem foldl_stepW_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [stepW]; omega)]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem foldl_take_getD (gs : List Gate) (w : List Bool) (t i : ℕ)
    (hi : i < ((gs.take t).foldl stepW w).length) :
    (gs.foldl stepW w).getD i false = ((gs.take t).foldl stepW w).getD i false := by
  conv_lhs => rw [← List.take_append_drop t gs, List.foldl_append]
  exact foldl_stepW_getD _ _ _ hi

theorem gate_val (C : Circuit) (x : Fin N → Bool) (t : ℕ) (ht : t < C.gates.length) :
    (C.wires (List.ofFn x)).getD (N + t) false =
      (C.gates[t]).op.eval ((C.gates[t]).inputs.map fun i =>
        if i < N + t then (C.wires (List.ofFn x)).getD i false else false) := by
  have hsplit : C.gates = C.gates.take t ++ C.gates[t] :: C.gates.drop (t + 1) := by
    simp [List.take_append_drop]
  have hlen : ((C.gates.take t).foldl stepW (List.ofFn x)).length = N + t := by
    rw [foldl_stepW_length, List.length_ofFn, List.length_take, Nat.min_eq_left ht.le]
  have hlhs : (C.wires (List.ofFn x)).getD (N + t) false =
      (C.gates[t]).op.eval ((C.gates[t]).inputs.map fun i =>
        ((C.gates.take t).foldl stepW (List.ofFn x)).getD i false) := by
    change (C.gates.foldl stepW (List.ofFn x)).getD (N + t) false = _
    conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
    rw [foldl_stepW_getD _ _ _ (by simp only [stepW, List.length_append, List.length_singleton, hlen]; omega)]
    simp only [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : ((C.gates.take t).foldl stepW (List.ofFn x)).length ≤ N + t), hlen, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hlhs]
  congr 1
  apply List.map_congr_left
  intro i _
  split_ifs with hi
  · exact (foldl_take_getD C.gates (List.ofFn x) t i (by omega)).symm
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem input_val (C : Circuit) (x : Fin N → Bool) (i : Fin N) :
    (C.wires (List.ofFn x)).getD i.val false = x i := by
  change (C.gates.foldl stepW (List.ofFn x)).getD i.val false = x i
  rw [foldl_stepW_getD _ _ _ (by simp)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

section Wires

variable {N : ℕ} {gates : List Gate} {ev : ℕ → (Fin N → Bool) → Bool}
variable (hev : ∀ w x, ev w x = (Circuit.mk gates w).eval (List.ofFn x))

include hev

theorem ev_input (x : Fin N → Bool) (i : Fin N) : ev i.val x = x i := by
  rw [hev]
  exact input_val (Circuit.mk gates i.val) x i

theorem ev_out_of_bounds (x : Fin N → Bool) (w : ℕ) (h : N + gates.length ≤ w) :
    ev w x = false := by
  rw [hev, Circuit.eval, Circuit.wires]
  change (gates.foldl stepW (List.ofFn x)).getD w false = false
  rw [List.getD_eq_default]
  simpa [foldl_stepW_length] using h

theorem ev_gate (x : Fin N → Bool) (i : Fin gates.length)
    (hi : ∀ a ∈ (gates.get i).inputs, a < N + i.val) :
    ev (N + i.val) x = (gates.get i).op.eval ((gates.get i).inputs.map (fun w => ev w x)) := by
  rw [hev, Circuit.eval, gate_val (Circuit.mk gates (N + i.val)) x i.val i.isLt]
  congr 1
  apply List.map_congr_left
  intro a ha
  have hat : a < N + i.val := hi a ha
  rw [ite_eq_left hat, hev]
  rfl

theorem ev_or (x : Fin N → Bool) (i : Fin gates.length)
    (hi : ∀ a ∈ (gates.get i).inputs, a < N + i.val) (hop : (gates.get i).op = .or) :
    ev (N + i.val) x = true ↔ ∃ w ∈ (gates.get i).inputs, ev w x = true := by
  rw [ev_gate hev x i hi, hop]
  simp [GateOp.eval, List.any_eq_true]

theorem ev_and (x : Fin N → Bool) (i : Fin gates.length)
    (hi : ∀ a ∈ (gates.get i).inputs, a < N + i.val) (hop : (gates.get i).op = .and) :
    ev (N + i.val) x = true ↔ ∀ w ∈ (gates.get i).inputs, ev w x = true := by
  rw [ev_gate hev x i hi, hop]
  simp [GateOp.eval, List.all_eq_true]

theorem ev_or_pair (x : Fin N → Bool) (i : Fin gates.length)
    (hi : ∀ a ∈ (gates.get i).inputs, a < N + i.val) (hop : (gates.get i).op = .or)
    {u v : ℕ} (hs : (gates.get i).inputs = [u, v]) :
    ev (N + i.val) x = true ↔ ev u x = true ∨ ev v x = true := by
  rw [ev_or hev x i hi hop, hs]
  simp

theorem ev_or_inputs_false (x : Fin N → Bool) (i : Fin gates.length)
    (hi : ∀ a ∈ (gates.get i).inputs, a < N + i.val) (hop : (gates.get i).op = .or)
    (hf : ev (N + i.val) x = false) (w : ℕ) (hw : w ∈ (gates.get i).inputs) : ev w x = false := by
  cases h : ev w x
  · rfl
  · have ht := (ev_or hev x i hi hop).mpr ⟨w, hw, h⟩
    rw [hf] at ht
    contradiction

theorem ev_and_input_false (x : Fin N → Bool) (i : Fin gates.length)
    (hi : ∀ a ∈ (gates.get i).inputs, a < N + i.val) (hop : (gates.get i).op = .and)
    (hf : ev (N + i.val) x = false) : ∃ w ∈ (gates.get i).inputs, ev w x = false := by
  classical
  by_contra! h
  have ht := (ev_and hev x i hi hop).mpr (fun w hw => Bool.eq_true_of_not_eq_false (h w hw))
  rw [hf] at ht
  contradiction

end Wires

section Line

variable {N : ℕ} (line : Finset (Fin N)) (gates : List Gate) (ev : ℕ → (Fin N → Bool) → Bool)
variable (test : Fin N → Fin N → Bool)

def miss : Fin N → Bool := fun p => decide (p ∉ line)

def activeOr (i : Fin gates.length) : Prop :=
  (gates.get i).op = .or ∧ ev (N + i.val) (miss line) = false ∧
    ∃ u v : ℕ, (gates.get i).inputs = [u, v]

noncomputable def support (i : Fin gates.length) : Finset (Fin N) := by
  classical
  exact line.filter (fun p => activeOr line gates ev i ∧ ev (N + i.val) (test p) = true)

theorem support_subset (i : Fin gates.length) : support line gates ev test i ⊆ line := by
  classical
  exact Finset.filter_subset _ _

theorem mem_support {i : Fin gates.length} {p : Fin N} :
    p ∈ support line gates ev test i ↔ p ∈ line ∧ activeOr line gates ev i ∧
      ev (N + i.val) (test p) = true := by
  classical
  exact Finset.mem_filter

variable (hev : ∀ w x, ev w x = (Circuit.mk gates w).eval (List.ofFn x))
variable (hin : ∀ i : Fin gates.length, ∀ w ∈ (gates.get i).inputs, w < N + i.val)

include hev hin

theorem mem_support_pair {i : Fin gates.length} {p : Fin N} {u v : ℕ}
    (hop : (gates.get i).op = .or) (hf : ev (N + i.val) (miss line) = false)
    (hs : (gates.get i).inputs = [u, v]) :
    p ∈ support line gates ev test i ↔ p ∈ line ∧ (ev u (test p) = true ∨ ev v (test p) = true) := by
  rw [mem_support, ev_or_pair hev (test p) i (hin i) hop hs]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, ⟨hop, hf, u, v, hs⟩, h.2⟩⟩

theorem closed_iff (k : ℕ) (X : Finset (Fin N)) :
    Closed (support line gates ev test) k X ↔
      ∀ i : Fin gates.length, i.val < k → (gates.get i).op = .or →
        ev (N + i.val) (miss line) = false → ∀ c1 c2 : ℕ, (gates.get i).inputs = [c1, c2] →
        ∀ s ∈ line, ∀ s' ∈ line,
        (ev c1 (test s) = true ∨ ev c2 (test s) = true) →
        (ev c1 (test s') = true ∨ ev c2 (test s') = true) → (s ∈ X ↔ s' ∈ X) := by
  constructor
  · intro h i hi hor hf u v huv a ha b hb hea heb
    have hh := mem_support_pair line gates ev test hev hin (p := a) hor hf huv
    have hh' := mem_support_pair line gates ev test hev hin (p := b) hor hf huv
    exact h i hi a (hh.mpr ⟨ha, hea⟩) b (hh'.mpr ⟨hb, heb⟩)
  · intro h i hi a ha b hb
    have ha' := (mem_support line gates ev test).mp ha
    obtain ⟨hor, hf, u, v, huv⟩ := ha'.2.1
    have he := (mem_support_pair line gates ev test hev hin hor hf huv).mp ha
    have he' := (mem_support_pair line gates ev test hev hin hor hf huv).mp hb
    exact h i hi hor hf u v huv a he.1 b he'.1 he.2 he'.2

variable (hOps : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
variable (hRaw : ∀ a ∈ line, ∀ p ∈ line, test p a = true → a = p)

include hOps hRaw

theorem wire_connected (w k : ℕ) (hk : k ≤ gates.length) (hw : w < N + k)
    (hf : ev w (miss line) = false) (a : Fin N) (ha : a ∈ line) (b : Fin N) (hb : b ∈ line)
    (hea : ev w (test a) = true) (heb : ev w (test b) = true) :
    Together (support line gates ev test) k a b := by
  induction w using Nat.strong_induction_on generalizing k with
  | ind w ih =>
    by_cases hraw : w < N
    · let p : Fin N := ⟨w, hraw⟩
      change ev p.val (miss line) = false at hf
      change ev p.val (test a) = true at hea
      change ev p.val (test b) = true at heb
      rw [ev_input hev] at hf hea heb
      have hp : p ∈ line := by simpa [miss] using hf
      have e := (hRaw p hp a ha hea).symm.trans (hRaw p hp b hb heb)
      subst b
      exact Together.refl _ _ _
    · let i : Fin gates.length := ⟨w - N, by omega⟩
      have ewi : w = N + i.val := by dsimp [i]; omega
      have hi : i.val < k := by omega
      have hop := hOps _ (List.get_mem gates i)
      rw [ewi] at hf hea heb
      rcases hop.1 with hand | hor
      · obtain ⟨c, hc, hfc⟩ := ev_and_input_false hev _ i (hin i) hand hf
        have hca := (ev_and hev _ i (hin i) hand).mp hea c hc
        have hcb := (ev_and hev _ i (hin i) hand).mp heb c hc
        have hlt : c < w := ewi.symm ▸ hin i c hc
        exact ih c hlt k hk (hlt.trans hw) hfc hca hcb
      · have hlen := hop.2
        cases hlist : (gates.get i).inputs with
        | nil =>
          obtain ⟨v, hv, _⟩ := (ev_or hev _ i (hin i) hor).mp hea
          change v ∈ (gates.get i).inputs at hv
          rw [hlist] at hv
          simp at hv
        | cons c rest =>
          cases rest with
          | nil =>
            have hc : c ∈ (gates.get i).inputs := by rw [hlist]; simp
            have hfc := ev_or_inputs_false hev _ i (hin i) hor hf c hc
            have hca : ev c (test a) = true := by
              obtain ⟨v, hv, H⟩ := (ev_or hev _ i (hin i) hor).mp hea
              change v ∈ (gates.get i).inputs at hv
              rw [hlist] at hv
              have he : v = c := List.mem_singleton.mp hv
              simpa [he] using H
            have hcb : ev c (test b) = true := by
              obtain ⟨v, hv, H⟩ := (ev_or hev _ i (hin i) hor).mp heb
              change v ∈ (gates.get i).inputs at hv
              rw [hlist] at hv
              have he : v = c := List.mem_singleton.mp hv
              simpa [he] using H
            have hlt : c < w := ewi.symm ▸ hin i c hc
            exact ih c hlt k hk (hlt.trans hw) hfc hca hcb
          | cons d rest =>
            cases rest with
            | nil =>
              intro X hX
              have hActive : activeOr line gates ev i := ⟨hor, hf, c, d, hlist⟩
              exact hX i hi a ((mem_support line gates ev test).mpr ⟨ha, hActive, hea⟩)
                b ((mem_support line gates ev test).mpr ⟨hb, hActive, heb⟩)
            | cons z tail =>
              rw [hlist] at hlen
              simp at hlen

end Line


section Closure

variable {N : ℕ} (line : Finset (Fin N)) (gates : List Gate) (ev : ℕ → (Fin N → Bool) → Bool)
variable (test : Fin N → Fin N → Bool)
variable (hev : ∀ w x, ev w x = (Circuit.mk gates w).eval (List.ofFn x))
variable (hin : ∀ i : Fin gates.length, ∀ w ∈ (gates.get i).inputs, w < N + i.val)
variable (hOps : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
variable (hRaw : ∀ a ∈ line, ∀ p ∈ line, test p a = true → a = p)

include hev hin hOps hRaw

theorem same_parent_connected (i : Fin gates.length) (hor : (gates.get i).op = .or)
    (hf : ev (N + i.val) (miss line) = false) (w : ℕ) (hw : w ∈ (gates.get i).inputs)
    (a : Fin N) (ha : a ∈ line) (b : Fin N) (hb : b ∈ line)
    (hta : ev w (test a) = true) (htb : ev w (test b) = true) :
    Together (support line gates ev test) i.val a b :=
  wire_connected line gates ev test hev hin hOps hRaw w i.val i.isLt.le (hin i w hw)
    (ev_or_inputs_false hev _ i (hin i) hor hf w hw) a ha b hb hta htb

theorem support_two_classes (i : Fin gates.length) (a : Fin N) (ha : a ∈ (support line gates ev test) i)
    (b : Fin N) (hb : b ∈ (support line gates ev test) i) (c : Fin N) (hc : c ∈ (support line gates ev test) i) :
    Together (support line gates ev test) i.val a b ∨ Together (support line gates ev test) i.val a c ∨ Together (support line gates ev test) i.val b c := by
  have hActive := ((mem_support line gates ev test).mp ha).2.1
  obtain ⟨hor, hf, u, v, huv⟩ := hActive
  have hu : u ∈ (gates.get i).inputs := by rw [huv]; simp
  have hv : v ∈ (gates.get i).inputs := by rw [huv]; simp
  have hp (p : Fin N) := mem_support_pair line gates ev test hev hin (p := p) hor hf huv
  obtain ⟨haL, haP⟩ := (hp a).mp ha
  obtain ⟨hbL, hbP⟩ := (hp b).mp hb
  obtain ⟨hcL, hcP⟩ := (hp c).mp hc
  have connect := same_parent_connected line gates ev test hev hin hOps hRaw i hor hf
  rcases haP with haU | haV <;> rcases hbP with hbU | hbV <;> rcases hcP with hcU | hcV
  · exact Or.inl (connect u hu a haL b hbL haU hbU)
  · exact Or.inl (connect u hu a haL b hbL haU hbU)
  · exact Or.inr (Or.inl (connect u hu a haL c hcL haU hcU))
  · exact Or.inr (Or.inr (connect v hv b hbL c hcL hbV hcV))
  · exact Or.inr (Or.inr (connect u hu b hbL c hcL hbU hcU))
  · exact Or.inr (Or.inl (connect v hv a haL c hcL haV hcV))
  · exact Or.inl (connect v hv a haL b hbL haV hbV)
  · exact Or.inl (connect v hv a haL b hbL haV hbV)

omit hev hin hOps hRaw in
theorem separator {m k : ℕ} {P : Fin m → Finset (Fin N)} {a b : Fin N}
    (h : ¬ Together P k a b) : ∃ X : Finset (Fin N), Closed P k X ∧ a ∈ X ∧ b ∉ X := by
  classical
  have hex : ∃ X : Finset (Fin N), Closed P k X ∧ ¬(a ∈ X ↔ b ∈ X) := by
    by_contra! hn
    exact h (fun X hX => hn X hX)
  obtain ⟨X, hx, hdis⟩ := hex
  by_cases ha : a ∈ X
  · exact ⟨X, hx, ha, fun hb => hdis ⟨fun _ => hb, fun _ => ha⟩⟩
  · have hb : b ∈ X := by
      by_contra hb
      exact hdis ⟨fun h' => False.elim (ha h'), fun h' => False.elim (hb h')⟩
    refine ⟨Finset.univ \ X, ?_, by simp [ha], by simp [hb]⟩
    intro i hi c hc d hd
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact not_congr (hx i hi c hc d hd)

theorem merge_characterization (i : Fin gates.length) :
    ((gates.get i).op = .or ∧ ev (N + i.val) (miss line) = false ∧
      ∃ u v : ℕ, (gates.get i).inputs = [u, v] ∧
        ∃ a ∈ line, ∃ b ∈ line, ev u (test a) = true ∧ ev v (test b) = true ∧
          ∃ X : Finset (Fin N), a ∈ X ∧ b ∉ X ∧ Closed (support line gates ev test) i.val X) ↔
    ∃ a ∈ (support line gates ev test) i, ∃ b ∈ (support line gates ev test) i, ¬ Together (support line gates ev test) i.val a b := by
  constructor
  · rintro ⟨hor, hf, u, v, huv, a, ha, b, hb, hea, heb, X, hAX, hBX, hClosed⟩
    have hmem (p : Fin N) := mem_support_pair line gates ev test hev hin (p := p) hor hf huv
    exact ⟨a, (hmem a).mpr ⟨ha, Or.inl hea⟩, b, (hmem b).mpr ⟨hb, Or.inr heb⟩,
      fun h => hBX ((h X hClosed).mp hAX)⟩
  · rintro ⟨a, ha, b, hb, hdis⟩
    obtain ⟨hor, hf, u, v, huv⟩ := ((mem_support line gates ev test).mp ha).2.1
    have hmem (p : Fin N) := mem_support_pair line gates ev test hev hin (p := p) hor hf huv
    obtain ⟨haL, haP⟩ := (hmem a).mp ha
    obtain ⟨hbL, hbP⟩ := (hmem b).mp hb
    have hu : u ∈ (gates.get i).inputs := by rw [huv]; simp
    have hv : v ∈ (gates.get i).inputs := by rw [huv]; simp
    have connect := same_parent_connected line gates ev test hev hin hOps hRaw i hor hf
    refine ⟨hor, hf, u, v, huv, ?_⟩
    rcases haP with haU | haV <;> rcases hbP with hbU | hbV
    · exact False.elim (hdis (connect u hu a haL b hbL haU hbU))
    · obtain ⟨X, hx, hAX, hBX⟩ := separator hdis
      exact ⟨a, haL, b, hbL, haU, hbV, X, hAX, hBX, hx⟩
    · obtain ⟨X, hx, hBX, hAX⟩ := separator (fun h => hdis h.symm)
      exact ⟨b, hbL, a, haL, hbU, haV, X, hBX, hAX, hx⟩
    · exact False.elim (hdis (connect v hv a haL b hbL haV hbV))

end Closure

section Geometry

variable {N : ℕ} (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N)

def admissible (x : Fin N → Bool) : Prop :=
  x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true

theorem line_of_both (hIntersection : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (hp01 : p0 ≠ p1) (hp0 : p0 ∈ L i0) (hp1 : p1 ∈ L i0)
    (t : Fin N) (h0 : p0 ∈ L t) (h1 : p1 ∈ L t) : t = i0 := by
  by_contra ht
  have htwo : 1 < (L t ∩ L i0).card := Finset.one_lt_card.mpr
    ⟨p0, Finset.mem_inter.mpr ⟨h0, hp0⟩, p1, Finset.mem_inter.mpr ⟨h1, hp1⟩, hp01⟩
  rw [hIntersection t i0 ht] at htwo
  omega

theorem miss_admissible (hIntersection : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (hp01 : p0 ≠ p1) (hp0 : p0 ∈ L i0) (hp1 : p1 ∈ L i0) (t : Fin N) :
    admissible L i0 p0 p1 (miss (L t)) := by
  classical
  by_cases h0 : p0 ∈ L t
  · by_cases h1 : p1 ∈ L t
    · have h := line_of_both L i0 p0 p1 hIntersection hp01 hp0 hp1 t h0 h1
      subst t
      exact Or.inr (Or.inr (fun u hu => decide_eq_true hu))
    · exact Or.inr (Or.inl (decide_eq_true h1))
  · exact Or.inl (decide_eq_true h0)

def TestSpec (T : Fin N → Fin N → Fin N → Bool) : Prop :=
  ∀ t p a : Fin N, T t p a = true ↔ (a = p ∨
    (p0 ∉ L t ∧ p ≠ p1 ∧ a = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ a = p1) ∨
    (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ a ∉ L t))

theorem test_inside_eq {T : Fin N → Fin N → Fin N → Bool} (hT : TestSpec L p0 p1 T)
    (t : Fin N) (a : Fin N) (ha : a ∈ L t) (p : Fin N) (h : T t p a = true) : a = p := by
  rcases (hT t p a).mp h with rfl | ⟨h0, _, rfl⟩ | ⟨_, h1, _, rfl⟩ | ⟨_, _, _, _, hout⟩
  · rfl
  · exact False.elim (h0 ha)
  · exact False.elim (h1 ha)
  · exact False.elim (hout ha)

theorem test_admissible {T : Fin N → Fin N → Fin N → Bool} (hT : TestSpec L p0 p1 T)
    (hIntersection : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (hp01 : p0 ≠ p1) (hp0 : p0 ∈ L i0) (hp1 : p1 ∈ L i0) (t p : Fin N) :
    admissible L i0 p0 p1 (T t p) := by
  classical
  by_cases he0 : p = p0
  · exact Or.inl ((hT t p p0).mpr (Or.inl he0.symm))
  by_cases he1 : p = p1
  · exact Or.inr (Or.inl ((hT t p p1).mpr (Or.inl he1.symm)))
  by_cases h0 : p0 ∈ L t
  · by_cases h1 : p1 ∈ L t
    · have he := line_of_both L i0 p0 p1 hIntersection hp01 hp0 hp1 t h0 h1
      refine Or.inr (Or.inr (fun a ha => (hT t p a).mpr (Or.inr (Or.inr (Or.inr ?_)))))
      exact ⟨h0, h1, he0, he1, he.symm ▸ ha⟩
    · exact Or.inr (Or.inl ((hT t p p1).mpr (Or.inr (Or.inr (Or.inl ⟨h0, h1, he0, rfl⟩)))))
  · exact Or.inl ((hT t p p0).mpr (Or.inr (Or.inl ⟨h0, he1, rfl⟩)))

theorem output_connected {T : Fin N → Fin N → Fin N → Bool} (hT : TestSpec L p0 p1 T)
    (hIntersection : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (hp01 : p0 ≠ p1) (hp0 : p0 ∈ L i0) (hp1 : p1 ∈ L i0)
    (t : Fin N) (hne : (L t).Nonempty)
    (gates : List Gate) (ev : ℕ → (Fin N → Bool) → Bool)
    (hev : ∀ w x, ev w x = (Circuit.mk gates w).eval (List.ofFn x))
    (hin : ∀ i : Fin gates.length, ∀ w ∈ (gates.get i).inputs, w < N + i.val)
    (hOps : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (o : ℕ) (ho : ∀ x, admissible L i0 p0 p1 x → ev o x = decide (∃ v ∈ L t, x v = true)) :
    ∀ a ∈ L t, ∀ b ∈ L t, Together (support (L t) gates ev (T t)) gates.length a b := by
  have hm : ev o (miss (L t)) = false := by
    rw [ho _ (miss_admissible L i0 p0 p1 hIntersection hp01 hp0 hp1 t)]
    simp [miss]
  have ht (p : Fin N) (hp : p ∈ L t) : ev o (T t p) = true := by
    rw [ho _ (test_admissible L i0 p0 p1 hT hIntersection hp01 hp0 hp1 t p)]
    exact decide_eq_true ⟨p, hp, (hT t p p).mpr (Or.inl rfl)⟩
  have hb : o < N + gates.length := by
    by_contra! hn
    obtain ⟨p, hp⟩ := hne
    have eq := ht p hp
    rw [ev_out_of_bounds hev _ _ hn] at eq
    contradiction
  intro a ha b hb'
  have hRaw : ∀ x ∈ L t, ∀ p ∈ L t, T t p x = true → x = p :=
    fun x hx p _ h => test_inside_eq L p0 p1 hT t x hx p h
  exact wire_connected (L t) gates ev (T t) hev hin hOps hRaw o gates.length le_rfl hb hm a ha b hb'
    (ht a ha) (ht b hb')

end Geometry

private lemma countClosedSucc {α : Type*} {m k : ℕ}
    (S : Fin m → Finset α) (j : Fin m) (hj : j.val = k) (X : Finset α) :
    Closed S (k + 1) X ↔
      Closed S k X ∧ (∀ a ∈ S j, ∀ b ∈ S j, (a ∈ X ↔ b ∈ X)) := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), h j (by omega)⟩
  · rintro ⟨h, h'⟩ i hi
    by_cases hlt : i.val < k
    · exact h i hlt
    · have he : i = j := Fin.ext (by omega)
      subst i
      exact h'

private lemma countIndexSucc {m k : ℕ} (I : Finset (Fin m))
    (j : Fin m) (hj : j.val = k) :
    (I.filter fun g => g.val < k + 1).card =
      (I.filter fun g => g.val < k).card + if j ∈ I then 1 else 0 := by
  classical
  by_cases hI : j ∈ I
  · have hs : (I.filter fun g => g.val < k + 1) =
        insert j (I.filter fun g => g.val < k) := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hg, hlt⟩
        by_cases h : g.val < k
        · exact Or.inr ⟨hg,h⟩
        · exact Or.inl (Fin.ext (by omega))
      · rintro (rfl | ⟨hg,h⟩)
        · exact ⟨hI, by omega⟩
        · exact ⟨hg, by omega⟩
    have hnot : j ∉ (I.filter fun g => g.val < k) := by simp [hj]
    rw [hs, Finset.card_insert_of_notMem hnot, ite_eq_left hI]
  · have hs : (I.filter fun g => g.val < k + 1) =
        (I.filter fun g => g.val < k) := by
      ext g
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hg, hlt⟩
        refine ⟨hg, ?_⟩
        by_contra nh
        have he : g = j := Fin.ext (by omega)
        exact hI (he ▸ hg)
      · rintro ⟨hg, hlt⟩
        exact ⟨hg, by omega⟩
    rw [hs, ite_eq_right hI, Nat.add_zero]

theorem mergeCard {α : Type*} {m : ℕ} (V : Finset α) (S : Fin m → Finset α)
    (I : Finset (Fin m)) (hV : V.Nonempty) (hsub : ∀ g, S g ⊆ V)
    (htwo : ∀ g, ∀ a ∈ S g, ∀ b ∈ S g, ∀ c ∈ S g,
      Together S g.val a b ∨ Together S g.val a c ∨ Together S g.val b c)
    (hend : ∀ a ∈ V, ∀ b ∈ V, Together S m a b)
    (hI : ∀ g, g ∈ I ↔ ∃ a ∈ S g, ∃ b ∈ S g, ¬ Together S g.val a b) :
    I.card + 1 = V.card := by
  classical
  have invariant (k : ℕ) (hk : k ≤ m) : ∃ f : α → α,
      (∀ a ∈ V, ∀ b ∈ V, f a = f b ↔ Together S k a b) ∧
      (V.image f).card + (I.filter fun g => g.val < k).card = V.card := by
    induction k with
    | zero =>
      refine ⟨id, ?_, by simp⟩
      intro a ha b hb
      change a = b ↔ Together S 0 a b
      constructor
      · rintro rfl X _
        rfl
      · intro hab
        have hh := hab {a} (by intro i hi; omega)
        exact (Finset.mem_singleton.mp (hh.mp (Finset.mem_singleton_self a))).symm
    | succ k ih =>
      obtain ⟨f, hf, hcard⟩ := ih (by omega)
      let j : Fin m := ⟨k, by omega⟩
      have hj : j.val = k := rfl
      have hcut := countIndexSucc I j hj
      by_cases hij : j ∈ I
      · obtain ⟨a, ha, b, hb, hneq⟩ := (hI j).mp hij
        have haV := hsub j ha
        have hbV := hsub j hb
        have hab : f a ≠ f b := fun eq => hneq ((hf a haV b hbV).mp eq)
        have hclass (z : α) (hz : z ∈ S j) : f z = f a ∨ f z = f b := by
          have hzV := hsub j hz
          rcases htwo j a ha b hb z hz with h | h | h
          · exact (hneq h).elim
          · exact Or.inl (((hf a haV z hzV).mpr h).symm)
          · exact Or.inr (((hf b hbV z hzV).mpr h).symm)
        let g (z : α) : α := if f z = f b then f a else f z
        have hconst (z : α) (hz : z ∈ S j) : g z = f a := by
          rcases hclass z hz with he | he
          · simp [g, he, hab]
          · simp [g, he]
        refine ⟨g, ?_, ?_⟩
        · intro x hx y hy
          constructor
          · intro e X hX
            obtain ⟨hold, hnew⟩ := (countClosedSucc S j hj X).mp hX
            have merge := hnew a ha b hb
            have old (u : α) (hu : u ∈ V) (v : α) (hv : v ∈ V)
                (he : f u = f v) : (u ∈ X ↔ v ∈ X) := (hf u hu v hv).mp he X hold
            by_cases hxb : f x = f b <;> by_cases hyb : f y = f b
            · exact old x hx y hy (hxb.trans hyb.symm)
            · have hay : f a = f y := by simpa [g, hxb, hyb] using e
              exact (old x hx b hbV hxb).trans (merge.symm.trans (old a haV y hy hay))
            · have hxa : f x = f a := by simpa [g, hxb, hyb] using e
              exact (old x hx a haV hxa).trans (merge.trans (old b hbV y hy hyb.symm))
            · exact old x hx y hy (by simpa [g, hxb, hyb] using e)
          · intro e
            let X := V.filter fun z => g z = g x
            have hX : Closed S (k + 1) X := by
              apply (countClosedSucc S j hj X).mpr
              constructor
              · intro i hi z hz w hw
                have hzw : Together S k z w := fun Y hY => hY i hi z hz w hw
                have hzw' := (hf z (hsub i hz) w (hsub i hw)).mpr hzw
                have hgw : g z = g w := by simp [g, hzw']
                simp [X, hsub i hz, hsub i hw, hgw]
              · intro z hz w hw
                have hgw := (hconst z hz).trans (hconst w hw).symm
                simp [X, hsub j hz, hsub j hw, hgw]
            have hnew := (e X hX).mp (by simp [X, hx])
            exact (Finset.mem_filter.mp hnew).2.symm
        · have heq : V.image g = (V.image f).erase (f b) := by
            ext value
            constructor
            · intro hm
              obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hm
              by_cases hxb : f x = f b
              · simpa [g, hxb] using
                  (Finset.mem_erase.mpr ⟨hab, Finset.mem_image_of_mem f haV⟩)
              · simpa [g, hxb] using
                  (Finset.mem_erase.mpr ⟨hxb, Finset.mem_image_of_mem f hx⟩)
            · intro hm
              obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hm
              obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hmem
              exact Finset.mem_image.mpr ⟨x, hx, by simp [g, hne]⟩
          have hbim : f b ∈ V.image f := Finset.mem_image_of_mem f hbV
          have hpos : 0 < (V.image f).card := Finset.card_pos.mpr ⟨f b, hbim⟩
          rw [heq, Finset.card_erase_of_mem hbim, hcut, ite_eq_left hij]
          omega
      · refine ⟨f, ?_, ?_⟩
        · have hsame (X : Finset α) (hX : Closed S k X) : Closed S (k + 1) X := by
            apply (countClosedSucc S j hj X).mpr
            refine ⟨hX, ?_⟩
            intro a ha b hb
            have hab : Together S k a b := by
              by_contra hn
              exact hij ((hI j).mpr ⟨a,ha,b,hb,hn⟩)
            exact hab X hX
          intro a ha b hb
          constructor
          · intro e X hX
            exact (hf a ha b hb).mp e X ((countClosedSucc S j hj X).mp hX).1
          · intro h
            exact (hf a ha b hb).mpr (fun X hX => h X (hsame X hX))
        · rwa [hcut, ite_eq_right hij, Nat.add_zero]
  obtain ⟨f, hf, hcard⟩ := invariant m le_rfl
  obtain ⟨a, ha⟩ := hV
  have him : V.image f = {f a} := by
    ext b
    constructor
    · intro h
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_singleton.mpr ((hf x hx a ha).mpr (hend x hx a ha))
    · intro h
      have he := Finset.mem_singleton.mp h
      subst b
      exact Finset.mem_image_of_mem f ha
  have hfilter : (I.filter fun g => g.val < m) = I := by
    ext g
    simp
  rw [him, hfilter] at hcard
  simpa [Nat.add_comm] using hcard

end PEqualNP.Outside.L_meta_1635

open PEqualNP.Outside.L_meta_1635 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_1635 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 p0 p1 : Fin N),
    3 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    p0 ≠ p1 → p0 ∈ L i0 → p1 ∈ L i0 →
    ∀ T : Fin N → Fin N → Fin N → Bool,
    (∀ (t p v : Fin N), T t p v = true ↔ (v = p ∨ (p0 ∉ L t ∧ p ≠ p1 ∧ v = p0) ∨ (p0 ∈ L t ∧ p1 ∉ L t ∧ p ≠ p0 ∧ v = p1) ∨
      (p0 ∈ L t ∧ p1 ∈ L t ∧ p ≠ p0 ∧ p ≠ p1 ∧ v ∉ L t))) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ gt.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, 1 ≤ (gates.get i).inputs.length) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    ∀ ev : ℕ → (Fin N → Bool) → Bool, (∀ (w : ℕ) (x : Fin N → Bool), ev w x = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, w⟩ (List.ofFn x)) →
    ∀ o : Fin N → ℕ, (∀ (t : Fin N) (x : Fin N → Bool), (x p0 = true ∨ x p1 = true ∨ ∀ u : Fin N, u ∉ L i0 → x u = true) →
      ev (o t) x = decide (∃ v ∈ L t, x v = true)) →
    ∀ Mg : Fin N → Fin gates.length → Prop,
    (∀ (t : Fin N) (g : Fin gates.length), Mg t g ↔ ((gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = false ∧
        ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ L t, ∃ r' ∈ L t, ev w1 (T t r) = true ∧ ev w2 (T t r') = true ∧
        ∃ X : Finset (Fin N), r ∈ X ∧ r' ∉ X ∧ (∀ i : Fin gates.length, i < g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = false →
          ∀ c1 c2 : ℕ, (gates.get i).inputs = [c1, c2] → ∀ s ∈ L t, ∀ s' ∈ L t,
          (ev c1 (T t s) = true ∨ ev c2 (T t s) = true) → (ev c1 (T t s') = true ∨ ev c2 (T t s') = true) → (s ∈ X ↔ s' ∈ X)))) →
    ∀ t : Fin N,
      (∀ g : Fin gates.length, ev (N + (g : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = false → ∀ a ∈ L t, ∀ b ∈ L t, ev (N + (g : ℕ)) (T t a) = true → ev (N + (g : ℕ)) (T t b) = true →
        ∀ X : Finset (Fin N), (∀ i : Fin gates.length, i ≤ g → (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or → ev (N + (i : ℕ)) (fun v : Fin N => decide (v ∉ L t)) = false →
          ∀ c1 c2 : ℕ, (gates.get i).inputs = [c1, c2] → ∀ s ∈ L t, ∀ s' ∈ L t,
          (ev c1 (T t s) = true ∨ ev c2 (T t s) = true) → (ev c1 (T t s') = true ∨ ev c2 (T t s') = true) → (s ∈ X ↔ s' ∈ X)) → (a ∈ X ↔ b ∈ X)) ∧
      ∀ I : Finset (Fin gates.length), (∀ g : Fin gates.length, g ∈ I ↔ Mg t g) → I.card = q := by
  intro q N L i0 p0 p1 _ _ hSize hIntersection _ hp01 hp0 hp1 T hT gates hOps _ hin ev hev o ho Mg hMg t
  let S := support (L t) gates ev (T t)
  have hRaw : ∀ a ∈ L t, ∀ p ∈ L t, T t p a = true → a = p :=
    fun a ha p _ h => test_inside_eq L p0 p1 hT t a ha p h
  constructor
  · intro g hf a ha b hb hA hB X hX
    have hTogether : Together S (g.val + 1) a b :=
      wire_connected (L t) gates ev (T t) hev hin hOps hRaw (N + g.val) (g.val + 1)
        g.isLt (by omega) hf a ha b hb hA hB
    apply hTogether X
    apply (closed_iff (L t) gates ev (T t) hev hin (g.val + 1) X).mpr
    intro i hi
    exact hX i (by change i.val ≤ g.val; omega)
  · intro I hI
    have hne : (L t).Nonempty := Finset.card_pos.mp (by rw [hSize]; omega)
    have htwo : ∀ i : Fin gates.length, ∀ a ∈ S i, ∀ b ∈ S i, ∀ c ∈ S i,
        Together S i.val a b ∨ Together S i.val a c ∨ Together S i.val b c :=
      support_two_classes (L t) gates ev (T t) hev hin hOps hRaw
    have hend : ∀ a ∈ L t, ∀ b ∈ L t, Together S gates.length a b :=
      output_connected L i0 p0 p1 hT hIntersection hp01 hp0 hp1 t hne gates ev hev hin hOps (o t) (ho t)
    have hmatch (g : Fin gates.length) : g ∈ I ↔ ∃ a ∈ S g, ∃ b ∈ S g, ¬ Together S g.val a b := by
      rw [hI g]
      change Mg t g ↔ ∃ a ∈ support (L t) gates ev (T t) g,
        ∃ b ∈ support (L t) gates ev (T t) g, ¬ Together (support (L t) gates ev (T t)) g.val a b
      rw [← merge_characterization (L t) gates ev (T t) hev hin hOps hRaw g]
      simp only [closed_iff (L t) gates ev (T t) hev hin]
      unfold miss
      exact hMg t g
    have hcard := mergeCard (L t) S I hne (support_subset (L t) gates ev (T t)) htwo hend hmatch
    rw [hSize] at hcard
    omega
