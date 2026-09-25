module

public import FormalConjecturesForMathlib.Computability.Complexity

/-!
# P ⊆ NP

We prove `ComplexityTheory.P ⊆ ComplexityTheory.NP` for the definitions of `P` and `NP` in
`FormalConjecturesForMathlib.Computability.Complexity`.

The key step is `IsPolyTime.comp_fst`: if `f : α → Bool` is computable in polynomial time,
then so is `fun p : α × β => f p.1`. Mathlib does not yet provide composition of Turing
machines, so we build the machine explicitly. The pair `(a, b)` is encoded as
`delimit (bitEncode a) ++ bitEncode b`. The new machine

1. parses the self-delimiting block `delimit (bitEncode a)` and pushes its payload onto an
   auxiliary stack;
2. erases the rest of the input (the encoding of `b`);
3. moves the auxiliary stack onto the input stack of the decider for `f`, restoring the order;
4. simulates the decider step by step.

Given a decider `f` for `L`, the verifier `fun (x, w) => f x` ignores the witness `w`.
-/

@[expose] public section

open Computability Turing StateTransition BitstringEncoding

namespace ComplexityTheory.PSubsetNP

/-! ### The machine -/

/-- Labels of the new machine. -/
inductive VLabel (Λ : Type)
  | old (l : Λ)
  | parse
  | erase
  | move
  | pushIn (a : Bool)
  deriving Fintype

section Machine

variable (tm : FinTM2)

/-- Stack alphabets: `none` is the new input stack, `some none` is an auxiliary stack, and
`some (some k)` are the stacks of the simulated machine. -/
abbrev VΓ : Option (Option tm.K) → Type
  | none => Bool
  | some none => Bool
  | some (some k) => tm.Γ k

/-- Internal states: a state of the simulated machine and a register for a popped bit. -/
abbrev Vσ : Type := tm.σ × Option Bool

/-- Build the stacks of the new machine. -/
def mkStk (L R : List Bool) (S : ∀ k, List (tm.Γ k)) : ∀ k, List (VΓ tm k)
  | none => L
  | some none => R
  | some (some k) => S k

/-- Lift a statement of the simulated machine to the new machine. -/
def liftStmt : TM2.Stmt tm.Γ tm.Λ tm.σ → TM2.Stmt (VΓ tm) (VLabel tm.Λ) (Vσ tm)
  | .push k f q => .push (some (some k)) (fun s => f s.1) (liftStmt q)
  | .peek k f q => .peek (some (some k)) (fun s o => (f s.1 o, s.2)) (liftStmt q)
  | .pop k f q => .pop (some (some k)) (fun s o => (f s.1 o, s.2)) (liftStmt q)
  | .load a q => .load (fun s => (a s.1, s.2)) (liftStmt q)
  | .branch p q₁ q₂ => .branch (fun s => p s.1) (liftStmt q₁) (liftStmt q₂)
  | .goto l => .goto (fun s => .old (l s.1))
  | .halt => .halt

variable (e : tm.Γ tm.k₀ ≃ Bool)

/-- The program of the new machine. -/
def vProg : VLabel tm.Λ → TM2.Stmt (VΓ tm) (VLabel tm.Λ) (Vσ tm)
  | .old l => liftStmt tm (tm.m l)
  | .parse =>
    .pop none (fun s o => (s.1, o)) <|
      .branch (fun s => s.2 == some true)
        (.pop none (fun s o => (s.1, o)) <|
          .push (some none) (fun s => s.2.getD false) (.goto fun _ => .parse))
        (.goto fun _ => .erase)
  | .erase =>
    .pop none (fun s o => (s.1, o)) (.goto fun s => if s.2.isSome then .erase else .move)
  | .move =>
    .pop (some none) (fun s o => (s.1, o)) (.goto fun s =>
      match s.2 with
      | some a => .pushIn a
      | none => .old tm.main)
  | .pushIn a => .push (some (some tm.k₀)) (fun _ => e.symm a) (.goto fun _ => .move)

/-- The new machine: it keeps the first component of a pair and runs `tm` on it. -/
def vTM : FinTM2 :=
  haveI := tm.σFin
  haveI := tm.ΛFin
  haveI := tm.kFin
  haveI := tm.kDecidableEq
  { K := Option (Option tm.K)
    k₀ := none
    k₁ := some (some tm.k₁)
    Γ := VΓ tm
    Λ := VLabel tm.Λ
    main := .parse
    σ := Vσ tm
    initialState := (tm.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype Bool)
    m := vProg tm e }

end Machine

/-! ### Reachability in bounded time -/

/-- `a` reaches `b` under `f` in at most `n` steps. -/
def ReachesIn {σ : Type*} (f : σ → Option σ) (a b : σ) (n : ℕ) : Prop :=
  ∃ k ≤ n, (flip bind f)^[k] (some a) = some b

lemma ReachesIn.trans {σ : Type*} {f : σ → Option σ} {a b c : σ} {n m : ℕ}
    (h₁ : ReachesIn f a b n) (h₂ : ReachesIn f b c m) : ReachesIn f a c (n + m) := by
  obtain ⟨k₁, hk₁, e₁⟩ := h₁
  obtain ⟨k₂, hk₂, e₂⟩ := h₂
  exact ⟨k₂ + k₁, by omega, by rw [Function.iterate_add_apply, e₁, e₂]⟩

lemma ReachesIn.single {σ : Type*} {f : σ → Option σ} {a b : σ} (h : f a = some b) :
    ReachesIn f a b 1 :=
  ⟨1, le_rfl, by simpa [flip] using h⟩

lemma ReachesIn.mono {σ : Type*} {f : σ → Option σ} {a b : σ} {n m : ℕ}
    (h : ReachesIn f a b n) (hnm : n ≤ m) : ReachesIn f a b m := by
  obtain ⟨k, hk, e⟩ := h
  exact ⟨k, hk.trans hnm, e⟩

/-- A bound on the number of steps gives Mathlib's `EvalsToInTime`. -/
noncomputable def ReachesIn.toEvalsToInTime {σ : Type*} {f : σ → Option σ} {a b : σ}
    {n : ℕ} (h : ReachesIn f a b n) : EvalsToInTime f a (some b) n :=
  ⟨⟨Classical.choose h, (Classical.choose_spec h).2⟩, (Classical.choose_spec h).1⟩

/-! ### Correctness of the machine -/

section Correctness

variable (tm : FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)

@[simp] lemma update_mkStk_none (L L' R : List Bool) (S : ∀ k, List (tm.Γ k)) :
    Function.update (mkStk tm L R S) none L' = mkStk tm L' R S := by
  funext k
  rcases k with _ | _ | k <;> simp [mkStk, Function.update]

@[simp] lemma update_mkStk_aux (L R R' : List Bool) (S : ∀ k, List (tm.Γ k)) :
    Function.update (mkStk tm L R S) (some none) R' = mkStk tm L R' S := by
  funext k
  rcases k with _ | _ | k <;> simp [mkStk, Function.update]

@[simp] lemma update_mkStk_sim (L R : List Bool) (S : ∀ k, List (tm.Γ k)) (k : tm.K)
    (x : List (tm.Γ k)) :
    Function.update (mkStk tm L R S) (some (some k)) x =
      mkStk tm L R (Function.update S k x) := by
  funext j
  rcases j with _ | _ | j
  · simp [mkStk, Function.update]
  · simp [mkStk, Function.update]
  · by_cases h : j = k
    · subst h; simp [mkStk]
    · rw [Function.update_of_ne (by simpa using h)]
      show S j = Function.update S k x j
      rw [Function.update_of_ne h]

/-- The embedding of configurations of `tm` into configurations of the new machine. -/
def liftCfg (c : TM2.Cfg tm.Γ tm.Λ tm.σ) : TM2.Cfg (VΓ tm) (VLabel tm.Λ) (Vσ tm) :=
  ⟨c.l.map .old, (c.var, none), mkStk tm [] [] c.stk⟩

lemma stepAux_liftStmt (q : TM2.Stmt tm.Γ tm.Λ tm.σ) (v : tm.σ) (S : ∀ k, List (tm.Γ k)) :
    TM2.stepAux (liftStmt tm q) (v, none) (mkStk tm [] [] S) =
      liftCfg tm (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [liftStmt, TM2.stepAux]
    rw [← ih]
    congr 1
    exact update_mkStk_sim tm [] [] S k _
  | peek k f q ih => simp only [liftStmt, TM2.stepAux]; exact ih _ _
  | pop k f q ih =>
    simp only [liftStmt, TM2.stepAux]
    rw [← ih]
    congr 1
    exact update_mkStk_sim tm [] [] S k _
  | load a q ih => simp only [liftStmt, TM2.stepAux]; exact ih _ _
  | branch p q₁ q₂ ih₁ ih₂ =>
    simp only [liftStmt, TM2.stepAux]
    cases p v <;> simp [ih₁, ih₂]
  | goto l => rfl
  | halt => rfl

lemma step_liftCfg (c : TM2.Cfg tm.Γ tm.Λ tm.σ) :
    (vTM tm e).step (liftCfg tm c) = (tm.step c).map (liftCfg tm) := by
  rcases c with ⟨_ | l, v, S⟩
  · rfl
  · exact congrArg some (stepAux_liftStmt tm (tm.m l) v S)

lemma iterate_liftCfg (n : ℕ) (c : TM2.Cfg tm.Γ tm.Λ tm.σ) :
    (flip bind (vTM tm e).step)^[n] (some (liftCfg tm c)) =
      ((flip bind tm.step)^[n] (some c)).map (liftCfg tm) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    rcases (flip bind tm.step)^[n] (some c) with _ | d
    · rfl
    · exact step_liftCfg tm e d

/-- A configuration of the new machine at one of its own labels. -/
def cfg (l : VLabel tm.Λ) (L R : List Bool) (o : Option Bool) (S : ∀ k, List (tm.Γ k)) :
    (vTM tm e).Cfg :=
  ⟨some l, (tm.initialState, o), mkStk tm L R S⟩

lemma erase_reaches (L R : List Bool) (o : Option Bool) (S : ∀ k, List (tm.Γ k)) :
    ReachesIn (vTM tm e).step (cfg tm e .erase L R o S) (cfg tm e .move [] R none S)
      (L.length + 1) := by
  induction L generalizing o with
  | nil =>
    refine ReachesIn.single ?_
    change some (TM2.stepAux (vProg tm e .erase) _ (mkStk tm [] R S)) = _
    simp [vProg, cfg, mkStk]; rfl
  | cons b L ih =>
    refine ((ReachesIn.single ?_).trans (ih (some b))).mono (by simp; omega)
    change some (TM2.stepAux (vProg tm e .erase) _ (mkStk tm (b :: L) R S)) = _
    simp [vProg, cfg, mkStk]; rfl

lemma parse_reaches (x rest R : List Bool) (o : Option Bool) (S : ∀ k, List (tm.Γ k)) :
    ReachesIn (vTM tm e).step (cfg tm e .parse (delimit x ++ rest) R o S)
      (cfg tm e .move [] (x.reverse ++ R) none S) (x.length + rest.length + 2) := by
  induction x generalizing R o with
  | nil =>
    refine ((ReachesIn.single ?_).trans
      (erase_reaches tm e rest R (some false) S)).mono (by simp; omega)
    change some (TM2.stepAux (vProg tm e .parse) _ (mkStk tm (false :: rest) R S)) = _
    simp [vProg, cfg, mkStk]; rfl
  | cons c x ih =>
    have h1 : ReachesIn (vTM tm e).step (cfg tm e .parse (delimit (c :: x) ++ rest) R o S)
        (cfg tm e .parse (delimit x ++ rest) (c :: R) (some c) S) 1 := by
      refine ReachesIn.single ?_
      change some (TM2.stepAux (vProg tm e .parse) _
        (mkStk tm (true :: c :: (delimit x ++ rest)) R S)) = _
      simp [vProg, cfg, mkStk]; rfl
    have h2 := (h1.trans (ih (c :: R) (some c))).mono
      (show 1 + (x.length + rest.length + 2) ≤ (c :: x).length + rest.length + 2 by simp; omega)
    simpa using h2

lemma move_reaches (R : List Bool) (o : Option Bool) (S : ∀ k, List (tm.Γ k)) :
    ReachesIn (vTM tm e).step (cfg tm e .move [] R o S)
      ⟨some (.old tm.main), (tm.initialState, none),
        mkStk tm [] [] (Function.update S tm.k₀ (R.reverse.map e.symm ++ S tm.k₀))⟩
      (2 * R.length + 1) := by
  induction R generalizing o S with
  | nil =>
    refine ReachesIn.single ?_
    change some (TM2.stepAux (vProg tm e .move) _ (mkStk tm [] [] S)) = _
    simp [vProg, mkStk]; rfl
  | cons a R ih =>
    have h1 : ReachesIn (vTM tm e).step (cfg tm e .move [] (a :: R) o S)
        (cfg tm e .move [] R (some a) (Function.update S tm.k₀ (e.symm a :: S tm.k₀))) 2 := by
      refine (ReachesIn.single (b := cfg tm e (.pushIn a) [] R (some a) S) ?_).trans
        (ReachesIn.single ?_)
      · change some (TM2.stepAux (vProg tm e .move) _ (mkStk tm [] (a :: R) S)) = _
        simp [vProg, cfg, mkStk]; rfl
      · change some (TM2.stepAux (vProg tm e (.pushIn a)) _ (mkStk tm [] R S)) = _
        simp [vProg, cfg, mkStk]; rfl
    have h2 := h1.trans (ih (some a) (Function.update S tm.k₀ (e.symm a :: S tm.k₀)))
    simp only [Function.update_idem, Function.update_self] at h2
    have key : (a :: R).reverse.map e.symm ++ S tm.k₀ =
        R.reverse.map e.symm ++ e.symm a :: S tm.k₀ := by simp
    rw [key]
    exact h2.mono (by simp; omega)

lemma initList_vTM (s : List Bool) :
    initList (vTM tm e) (List.map (Equiv.refl Bool).invFun s) =
      cfg tm e .parse s [] none (fun _ => []) := by
  simp only [initList, cfg]
  congr 1
  funext k
  rcases k with _ | _ | k
  · exact List.map_id s
  · rfl
  · rfl

lemma liftCfg_initList (s : List (tm.Γ tm.k₀)) :
    liftCfg tm (initList tm s) = ⟨some (.old tm.main), (tm.initialState, none),
      mkStk tm [] [] (Function.update (fun _ => []) tm.k₀ s)⟩ := by
  simp only [liftCfg, initList, Option.map_some]
  congr 2
  funext k
  by_cases h : k = tm.k₀
  · subst h; simp
  · simp [h]

lemma haltList_vTM (s : List (tm.Γ tm.k₁)) :
    haltList (vTM tm e) s = liftCfg tm (haltList tm s) := by
  simp only [liftCfg, haltList, Option.map_none]
  congr 1
  funext k
  rcases k with _ | _ | k
  · rfl
  · rfl
  · by_cases h : k = tm.k₁
    · subst h; simp [mkStk, vTM]; rfl
    · simp [mkStk, vTM, h]

end Correctness

lemma _root_.Polynomial.eval_mono_nat (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval_add]; omega
  | monomial n c =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left h n)

end PSubsetNP

open PSubsetNP

/-- If `f` is computable in polynomial time, then so is `fun p => f p.1`. -/
theorem IsPolyTime.comp_fst {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    {f : α → Bool} (hf : IsPolyTime f) : IsPolyTime (fun p : α × β => f p.1) := by
  obtain ⟨h⟩ := hf
  refine ⟨⟨⟨vTM h.tm h.inputAlphabet, Equiv.refl _, h.outputAlphabet⟩,
    2 * Polynomial.X + 2 + h.time, fun x => ReachesIn.toEvalsToInTime ?_⟩⟩
  rcases x with ⟨a, b⟩
  change ReachesIn (vTM h.tm h.inputAlphabet).step
    (initList (vTM h.tm h.inputAlphabet)
      (List.map (Equiv.refl Bool).invFun (delimit (bitEncode a) ++ bitEncode b)))
    (haltList (vTM h.tm h.inputAlphabet)
      (List.map h.outputAlphabet.invFun (bitEncode (f a)))) _
  rw [initList_vTM]
  erw [haltList_vTM]
  have hA := parse_reaches h.tm h.inputAlphabet (bitEncode a) (bitEncode b) [] none
    (fun _ => [])
  have hB := move_reaches h.tm h.inputAlphabet ((bitEncode a).reverse ++ []) none (fun _ => [])
  obtain ⟨⟨k, hC⟩, hk⟩ := h.outputsFun a
  replace hk : k ≤ h.time.eval (bitEncode a).length := hk
  have hC' : ReachesIn (vTM h.tm h.inputAlphabet).step
      (liftCfg h.tm (initList h.tm (List.map h.inputAlphabet.invFun (bitEncode a))))
      (liftCfg h.tm (haltList h.tm (List.map h.outputAlphabet.invFun (bitEncode (f a)))))
      (h.time.eval (bitEncode a).length) :=
    ⟨k, hk, by erw [iterate_liftCfg]; exact congrArg (Option.map _) hC⟩
  rw [liftCfg_initList] at hC'
  simp only [List.append_nil, List.reverse_reverse] at hA hB
  refine (hA.trans (hB.trans hC')).mono ?_
  change _ ≤ Polynomial.eval (delimit (bitEncode a) ++ bitEncode b).length _
  have hlen : (delimit (bitEncode a) ++ bitEncode b).length =
      2 * (bitEncode a).length + 1 + (bitEncode b).length := by simp
  have hmono := Polynomial.eval_mono_nat h.time
    (show (bitEncode a).length ≤ (delimit (bitEncode a) ++ bitEncode b).length by omega)
  simp only [List.length_reverse, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_ofNat]
  omega

/-- **P ⊆ NP.** A decider for `L` gives a verifier that ignores the witness. -/
theorem P_subset_NP' : P ⊆ NP := by
  intro L hL
  refine ⟨0, fun p => L p.1, IsPolyTime.comp_fst hL, fun x => ?_⟩
  constructor
  · intro hx
    exact ⟨[], by simp, hx⟩
  · rintro ⟨w, -, hw⟩
    exact hw

end ComplexityTheory
