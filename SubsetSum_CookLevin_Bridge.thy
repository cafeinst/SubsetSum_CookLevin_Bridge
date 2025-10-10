theory SubsetSum_CookLevin_Bridge
  imports
    Main "Cook_Levin.NP" "SubsetSum_DTM_Bridge" "SubsetSum_DTM_Bridge2"
begin

text ‹
  This file provides a thin adapter from the Cook–Levin TM model
  to the TM interface expected by our coverage/steps proofs.
›

(***********************************************************)
(* 1. Interface to the CL machine model                    *)
(***********************************************************)

text ‹We assume the Cook–Levin library gives a (deterministic) TM value ‹M›
  together with its small-step semantics and acceptance predicate.›

locale CL_TM_Interface =
  fixes M_CL :: "'mach"               (* CL's machine value *)
  and   Σ    :: "'sym set"            (* tape alphabet if needed *)
  and   q_acc :: "'state"             (* accepting state, if exposed *)
  and   q_rej :: "'state"             (* rejecting state, if exposed *)
  assumes CL_deterministic: True
begin

text ‹Map Cook–Levin’s notions to the simple interface used by
  ‹DTM_Run_Sem› / your bridge proofs. The exact right-hand-sides
  depend on the CL library’s symbols; below are placeholders with
  clear names to fill.›

(* TOTAL STEPS TO HALT ON INPUT x *)
definition steps_CL :: "'mach ⇒ bool list ⇒ nat" where
  "steps_CL _ x = (SOME t. True)"  (* TODO: replace with CL run-length to halting *)

(* CONFIGURATION AFTER t STEPS *)
definition conf_CL :: "'mach ⇒ bool list ⇒ nat ⇒ 'conf" where
  "conf_CL _ x t = (undefined)"     (* TODO: map CL configuration type *)

(* HEAD POSITION ON THE INPUT TAPE *)
definition head0_CL :: "'conf ⇒ int" where
  "head0_CL C = 0"               (* TODO: project the head position from C *)

(* ACCEPTANCE PREDICATE *)
definition accepts_CL :: "'mach ⇒ bool list ⇒ bool" where
  "accepts_CL _ x = False"       (* TODO: use CL acceptance predicate *)

end  (* locale CL_TM_Interface *)

(***********************************************************)
(* 2. Bridge: show CL interface satisfies your TM axioms   *)
(***********************************************************)

text ‹We now package the four semantic obligations required by your
  ‹DTM_Run_Sem› locale, instantiating with the CL-backed primitives.›

locale CL_as_DTM_Run_Sem =
  fixes M_CL         :: "'mach"
    and steps_CL     :: "'mach ⇒ bool list ⇒ nat"
    and conf_CL      :: "'mach ⇒ bool list ⇒ nat ⇒ 'conf"
    and head0_CL     :: "'conf ⇒ int"
    and accepts_CL   :: "'mach ⇒ bool list ⇒ bool"
    and stepf_CL     :: "'conf ⇒ bool ⇒ 'conf"
    and final_acc_CL :: "'conf ⇒ bool"
  assumes step_sem_CL:
    "⋀x t. conf_CL M_CL x (Suc t)
         = stepf_CL (conf_CL M_CL x t) (x ! nat (head0_CL (conf_CL M_CL x t)))"
  assumes steps_stable_raw_CL:
    "⋀x y.
      (⋀i. i ∈ (λt. nat (head0_CL (conf_CL M_CL x t))) ` {..< steps_CL M_CL x} ⟹ x ! i = y ! i)
      ⟹ steps_CL M_CL x = steps_CL M_CL y"
  assumes accepts_sem_CL:
    "⋀x. accepts_CL M_CL x = final_acc_CL (conf_CL M_CL x (steps_CL M_CL x))"
  assumes conf0_same_CL:
    "⋀x y. conf_CL M_CL x 0 = conf_CL M_CL y 0"
begin

sublocale DTM_Run_Sem
  steps_CL conf_CL head0_CL accepts_CL M_CL stepf_CL final_acc_CL
  by (unfold_locales;
      (fact step_sem_CL steps_stable_raw_CL accepts_sem_CL conf0_same_CL)?)

end

definition Lval_at_CL ::
  " (int list ⇒ int ⇒ bool list)
  ⇒ (nat ⇒ int ⇒ bool list)
  ⇒ (bool list ⇒ int)
  ⇒ nat
  ⇒ int list ⇒ int ⇒ (nat ⇒ bool) ⇒ nat ⇒ int"
where
  "Lval_at_CL enc0 to_bits from_bits kk as s oL j =
     from_bits (map oL [ length (enc0 as s)
                       + offL as s j
                     ..< length (enc0 as s) + offL as s j + W as s ])"

definition Rval_at_CL ::
  " (int list ⇒ int ⇒ bool list)
  ⇒ (nat ⇒ int ⇒ bool list)
  ⇒ (bool list ⇒ int)
  ⇒ nat
  ⇒ int list ⇒ int ⇒ (nat ⇒ bool) ⇒ nat ⇒ int"
where
  "Rval_at_CL enc0 to_bits from_bits kk as s oR j =
     from_bits (map oR [ length (enc0 as s)
                       + offR as s kk j
                     ..< length (enc0 as s) + offR as s kk j + W as s ])"

definition Good_CL ::
  " (int list ⇒ int ⇒ bool list)
  ⇒ (nat ⇒ int ⇒ bool list)
  ⇒ (bool list ⇒ int)
  ⇒ nat
  ⇒ int list ⇒ int ⇒ (nat ⇒ bool) ⇒ (nat ⇒ bool) ⇒ bool"
where
  "Good_CL enc0 to_bits from_bits kk as s oL oR ≡
     (∃jL<length (enumL as s kk). ∃jR<length (enumR as s kk).
         Lval_at_CL enc0 to_bits from_bits kk as s oL jL
       = Rval_at_CL enc0 to_bits from_bits kk as s oR jR)"

(***********************************************************)
(* 3. Specialize your Coverage_TM with CL primitives       *)
(***********************************************************)

section ‹Cook–Levin bridge: reuse Coverage_TM without changing it›

locale CL_Cov_Params =
  fixes M' :: 'mach
    and steps' :: "'mach ⇒ bool list ⇒ nat"
    and conf'  :: "'mach ⇒ bool list ⇒ nat ⇒ 'conf"
    and head0' :: "'conf ⇒ int"
    and accepts' :: "'mach ⇒ bool list ⇒ bool"
    and stepf' :: "'conf ⇒ bool ⇒ 'conf"
    and final_acc' :: "'conf ⇒ bool"
    and enc0 :: "int list ⇒ int ⇒ bool list"
    and to_bits :: "nat ⇒ int ⇒ bool list"
    and from_bits :: "bool list ⇒ int"
    and kk :: nat
    and padL :: "int list ⇒ int ⇒ nat ⇒ bool list"
    and padR :: "int list ⇒ int ⇒ nat ⇒ bool list"
    and enc  :: "int list ⇒ int ⇒ nat ⇒ bool list"
  assumes step_sem':
    "⋀x t. conf' M' x (Suc t) =
           stepf' (conf' M' x t) (x ! nat (head0' (conf' M' x t)))"
  and steps_stable_raw':
    "⋀x y.
       (⋀i. i ∈ (λt. nat (head0' (conf' M' x t))) ` {..< steps' M' x} ⟹ x ! i = y ! i)
       ⟹ steps' M' x = steps' M' y"
  and accepts_sem':
    "⋀x. accepts' M' x = final_acc' (conf' M' x (steps' M' x))"
  and conf0_same':
    "⋀x y. conf' M' x 0 = conf' M' y 0"
  and bits_roundtrip':
    "⋀as s k v.
       v ∈ set (enumL as s k) ∪ set (enumR as s k) ⟹
       length (to_bits (W as s) v) = W as s ∧ from_bits (to_bits (W as s) v) = v"
  and read0_after_enc0':
  "⋀as s.
     image (λt. nat (head0' (conf' M' (enc as s kk) t)))
           {..< steps' M' (enc as s kk)}
   ⊆ { length (enc0 as s)
        ..< length (enc0 as s)
            + length (SubsetSum_Padded_Enc.padL to_bits as s kk)
            + length (SubsetSum_Padded_Enc.padR to_bits as s kk) }"
  and correctness_cov':
  "⋀as s. accepts' M' (enc as s kk) =
          Good_CL enc0 to_bits from_bits kk as s
            ((!) (enc as s kk)) ((!) (enc as s kk))"
  and padL_eq: "⋀as s k. padL as s k = SubsetSum_Padded_Enc.padL to_bits as s k"
  and padR_eq: "⋀as s k. padR as s k = SubsetSum_Padded_Enc.padR to_bits as s k"
  and enc_is_concrete:
    "⋀as s k. enc as s k = SubsetSum_Padded_Enc.enc enc0 to_bits as s k"
begin

(* Abbreviations to match the DTM/CL names *)
definition M_CL         where "M_CL = M'"
definition steps_CL     where "steps_CL = steps'"
definition conf_CL      where "conf_CL = conf'"
definition head0_CL     where "head0_CL = head0'"
definition accepts_CL   where "accepts_CL = accepts'"
definition stepf_CL     where "stepf_CL = stepf'"
definition final_acc_CL where "final_acc_CL = final_acc'"
definition x0 where
  "x0 as s ≡ SubsetSum_Padded_Enc.enc enc0 to_bits as s kk"

interpretation CL: CL_as_DTM_Run_Sem
  M_CL steps_CL conf_CL head0_CL accepts_CL stepf_CL final_acc_CL
proof (unfold_locales)
  show "⋀x t. conf_CL M_CL x (Suc t) =
              stepf_CL (conf_CL M_CL x t)
                       (x ! nat (head0_CL (conf_CL M_CL x t)))"
    unfolding conf_CL_def M_CL_def stepf_CL_def head0_CL_def
    by (fact step_sem')

  show "⋀x y.
         (⋀i. i ∈ (λt. nat (head0_CL (conf_CL M_CL x t))) ` {..< steps_CL M_CL x}
              ⟹ x ! i = y ! i)
         ⟹ steps_CL M_CL x = steps_CL M_CL y"
    unfolding head0_CL_def conf_CL_def steps_CL_def M_CL_def
    by (fact steps_stable_raw')

  show "⋀x. accepts_CL M_CL x =
            final_acc_CL (conf_CL M_CL x (steps_CL M_CL x))"
    unfolding accepts_CL_def M_CL_def final_acc_CL_def
              conf_CL_def steps_CL_def
    by (fact accepts_sem')

  show "⋀x y. conf_CL M_CL x 0 = conf_CL M_CL y 0"
    unfolding conf_CL_def M_CL_def
    by (fact conf0_same')
qed

interpretation Cov: Coverage_TM
  steps_CL conf_CL head0_CL accepts_CL
  M_CL     stepf_CL final_acc_CL
  enc0     to_bits  from_bits kk
proof (unfold_locales)

  (* 0) handy inclusion fact we’ll use for read-window confinement *)
  have incl:
  "(λt. nat (head0' (conf' M' (enc as s kk) t))) ` {..< steps' M' (enc as s kk)}
    ⊆ { length (enc0 as s) ..< length (enc0 as s)
      + length (SubsetSum_Padded_Enc.padL to_bits as s kk)
      + length (SubsetSum_Padded_Enc.padR to_bits as s kk) }"
    for as s
    unfolding head0_CL_def conf_CL_def steps_CL_def M_CL_def x0_def
    by (simp add: read0_after_enc0' padL_eq padR_eq)

  (* 1) bits round-trip *)
  show "⋀as s k v.
          v ∈ set (enumL as s k) ∪ set (enumR as s k) ⟹
          length (to_bits (W as s) v) = W as s ∧
          from_bits (to_bits (W as s) v) = v"
    by (rule bits_roundtrip')

  (* 2) acceptance equals Coverage_TM.good (rewrite through Good_CL) *)
  show "⋀as s. accepts_CL M_CL (SubsetSum_Padded_Enc.enc enc0 to_bits as s kk) =
         (∃jL<length (enumL as s kk).∃jR<length (enumR as s kk).
              from_bits
                (map ((!) (SubsetSum_Padded_Enc.enc enc0 to_bits as s kk))
                  [length (enc0 as s) + offL as s jL
                   ..< length (enc0 as s) + offL as s jL + W as s]) =
              from_bits
                (map ((!) (SubsetSum_Padded_Enc.enc enc0 to_bits as s kk))
                  [length (enc0 as s) + offR as s kk jR
                   ..< length (enc0 as s) + offR as s kk jR + W as s]))"
  proof-
    fix as s
    have A:
      "accepts_CL M_CL (x0 as s) =
       Good_CL enc0 to_bits from_bits kk as s
         ((!) (x0 as s)) ((!) (x0 as s))"
      unfolding M_CL_def accepts_CL_def x0_def using correctness_cov'
      by (simp add: enc_is_concrete)
    have B:
      "Good_CL enc0 to_bits from_bits kk as s
       ((!) (x0 as s)) ((!) (x0 as s)) =
        (∃jL<length (enumL as s kk).∃jR<length (enumR as s kk).
          from_bits (map ((!) (x0 as s))
                   [length (enc0 as s) + offL as s jL
                    ..< length (enc0 as s) + offL as s jL + W as s]) =
          from_bits (map ((!) (x0 as s))
                   [length (enc0 as s) + offR as s kk jR
                    ..< length (enc0 as s) + offR as s kk jR + W as s]))"
      by (simp add: Good_CL_def Lval_at_CL_def Rval_at_CL_def)
    from A B
    show "accepts_CL M_CL (SubsetSum_Padded_Enc.enc enc0 to_bits as s kk) =
        (∃jL<length (enumL as s kk).
           ∃jR<length (enumR as s kk).
             from_bits
               (map ((!) (SubsetSum_Padded_Enc.enc enc0 to_bits as s kk))
                 [length (enc0 as s) + offL as s jL
                  ..< length (enc0 as s) + offL as s jL + W as s]) =
             from_bits
               (map ((!) (SubsetSum_Padded_Enc.enc enc0 to_bits as s kk))
                 [length (enc0 as s) + offR as s kk jR
                  ..< length (enc0 as s) + offR as s kk jR + W as s]))"
      by (simp add: x0_def)
  qed

  (* 3) read-window confinement — NOTE: use CL.Base.read0, not DTM_Run_Sem.Base.read0 *)
  show "⋀as s.
    CL.Base.read0 M_CL (SubsetSum_Padded_Enc.enc enc0 to_bits as s kk) ⊆
    { length (enc0 as s) ..<
    length (enc0 as s)
    + length (SubsetSum_Padded_Enc.padL to_bits as s kk)
    + length (SubsetSum_Padded_Enc.padR to_bits as s kk) }"
  proof-
    fix as s
    have H:
    "(λt. nat (head0_CL
           (conf_CL M_CL (SubsetSum_Padded_Enc.enc enc0 to_bits as s kk) t))) `
     {..< steps_CL M_CL (SubsetSum_Padded_Enc.enc enc0 to_bits as s kk)} ⊆
     { length (enc0 as s) ..<
      length (enc0 as s)
      + length (SubsetSum_Padded_Enc.padL to_bits as s kk)
      + length (SubsetSum_Padded_Enc.padR to_bits as s kk) }"
      unfolding head0_CL_def conf_CL_def steps_CL_def M_CL_def
      using read0_after_enc0'[of as s]
      by (simp add: enc_is_concrete)
    show "CL.Base.read0 M_CL (SubsetSum_Padded_Enc.enc enc0 to_bits as s kk) ⊆
        { length (enc0 as s) ..<
          length (enc0 as s)
          + length (SubsetSum_Padded_Enc.padL to_bits as s kk)
          + length (SubsetSum_Padded_Enc.padR to_bits as s kk) }"
      using H by (simp add: CL.Base.read0_def)
  qed
  (* 4–6) definitional equations required by Coverage_TM *)
  show "⋀as s oL j.
       Lval_at as s oL j ≡
       from_bits
         (map oL [length (enc0 as s) + offL as s j
                  ..< length (enc0 as s) + offL as s j + W as s])"
  by (simp add: Coverage_TM.Lval_at_def)
  show "⋀as s oR j.
       Rval_at as s oR j ≡
       from_bits
         (map oR [length (enc0 as s) + offR as s kk j
                  ..< length (enc0 as s) + offR as s kk j + W as s])"
  by (simp add: Coverage_TM.Rval_at_def)
  show "⋀as s oL oR.
       good as s oL oR ≡
       (∃jL<length (enumL as s kk). ∃jR<length (enumR as s kk).
          Lval_at as s oL jL = Rval_at as s oR jR)"
  by (simp add: Coverage_TM.good_def)
qed
end
end
