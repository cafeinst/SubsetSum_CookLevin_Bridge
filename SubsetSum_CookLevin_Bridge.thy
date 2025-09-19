theory SubsetSum_CookLevin_Bridge
  imports
    Main "Cook_Levin.NP" "SubsetSum_DTM_Bridge"
begin

text \<open>
  This file provides a thin adapter from the Cook–Levin TM model
  to the TM interface expected by our coverage/steps proofs.
\<close>

(***********************************************************)
(* 1. Interface to the CL machine model                    *)
(***********************************************************)

text \<open>We assume the Cook–Levin library gives a (deterministic) TM value \<open>M\<close>
  together with its small-step semantics and acceptance predicate.\<close>

locale CL_TM_Interface =
  fixes M_CL :: "'mach"               (* CL's machine value *)
  and   \<Sigma>    :: "'sym set"            (* tape alphabet if needed *)
  and   q_acc :: "'state"             (* accepting state, if exposed *)
  and   q_rej :: "'state"             (* rejecting state, if exposed *)
  assumes CL_deterministic: True
begin

text \<open>Map Cook–Levin’s notions to the simple interface used by
  \<open>DTM_Run_Sem\<close> / your bridge proofs. The exact right-hand-sides
  depend on the CL library’s symbols; below are placeholders with
  clear names to fill.\<close>

(* TOTAL STEPS TO HALT ON INPUT x *)
definition steps_CL :: "'mach \<Rightarrow> bool list \<Rightarrow> nat" where
  "steps_CL _ x = (SOME t. True)"  (* TODO: replace with CL run-length to halting *)

(* CONFIGURATION AFTER t STEPS *)
definition conf_CL :: "'mach \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> 'conf" where
  "conf_CL _ x t = (undefined)"     (* TODO: map CL configuration type *)

(* HEAD POSITION ON THE INPUT TAPE *)
definition head0_CL :: "'conf \<Rightarrow> int" where
  "head0_CL C = 0"               (* TODO: project the head position from C *)

(* ACCEPTANCE PREDICATE *)
definition accepts_CL :: "'mach \<Rightarrow> bool list \<Rightarrow> bool" where
  "accepts_CL _ x = False"       (* TODO: use CL acceptance predicate *)

end  (* locale CL_TM_Interface *)

(***********************************************************)
(* 2. Bridge: show CL interface satisfies your TM axioms   *)
(***********************************************************)

text \<open>We now package the four semantic obligations required by your
  \<open>DTM_Run_Sem\<close> locale, instantiating with the CL-backed primitives.\<close>

locale CL_as_DTM_Run_Sem =
  fixes M_CL         :: "'mach"
    and steps_CL     :: "'mach \<Rightarrow> bool list \<Rightarrow> nat"
    and conf_CL      :: "'mach \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> 'conf"
    and head0_CL     :: "'conf \<Rightarrow> int"
    and accepts_CL   :: "'mach \<Rightarrow> bool list \<Rightarrow> bool"
    and stepf_CL     :: "'conf \<Rightarrow> bool \<Rightarrow> 'conf"
    and final_acc_CL :: "'conf \<Rightarrow> bool"
  assumes step_sem_CL:
    "\<And>x t. conf_CL M_CL x (Suc t)
         = stepf_CL (conf_CL M_CL x t) (x ! nat (head0_CL (conf_CL M_CL x t)))"
  assumes steps_stable_raw_CL:
    "\<And>x y.
      (\<And>i. i \<in> (\<lambda>t. nat (head0_CL (conf_CL M_CL x t))) ` {..< steps_CL M_CL x} \<Longrightarrow> x ! i = y ! i)
      \<Longrightarrow> steps_CL M_CL x = steps_CL M_CL y"
  assumes accepts_sem_CL:
    "\<And>x. accepts_CL M_CL x = final_acc_CL (conf_CL M_CL x (steps_CL M_CL x))"
  assumes conf0_same_CL:
    "\<And>x y. conf_CL M_CL x 0 = conf_CL M_CL y 0"
begin

sublocale DTM_Run_Sem
  steps_CL conf_CL head0_CL accepts_CL M_CL stepf_CL final_acc_CL
  by (unfold_locales;
      (fact step_sem_CL steps_stable_raw_CL accepts_sem_CL conf0_same_CL)?)

end

(***********************************************************)
(* 3. Specialize your Coverage_TM with CL primitives       *)
(***********************************************************)

section \<open>Cook–Levin bridge: reuse Coverage_TM without changing it\<close>

locale CL_Cov_Params =
  fixes M' :: 'mach
    and steps' :: "'mach \<Rightarrow> bool list \<Rightarrow> nat"
    and conf'  :: "'mach \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> 'conf"
    and head0' :: "'conf \<Rightarrow> int"
    and accepts' :: "'mach \<Rightarrow> bool list \<Rightarrow> bool"
    and stepf' :: "'conf \<Rightarrow> bool \<Rightarrow> 'conf"
    and final_acc' :: "'conf \<Rightarrow> bool"
    and enc0 :: "int list \<Rightarrow> int \<Rightarrow> bool list"
    and to_bits :: "nat \<Rightarrow> int \<Rightarrow> bool list"
    and from_bits :: "bool list \<Rightarrow> int"
    and kk :: nat
    and enc  :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool list"
    and padL :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool list"
    and padR :: "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool list"
  assumes step_sem':
    "\<And>x t. conf' M' x (Suc t) =
           stepf' (conf' M' x t) (x ! nat (head0' (conf' M' x t)))"
  and steps_stable_raw':
    "\<And>x y. (\<And>i. i \<in> (\<lambda>t. nat (head0' (conf' M' x t))) ` {..< steps' M' x} \<Longrightarrow> x ! i = y ! i)
           \<Longrightarrow> steps' M' x = steps' M' y"
  and accepts_sem':
    "\<And>x. accepts' M' x = final_acc' (conf' M' x (steps' M' x))"
  and conf0_same':
    "\<And>x y. conf' M' x 0 = conf' M' y 0"
  and bits_roundtrip':
    "\<And>as s k v.
       v \<in> set (enumL as s k) \<union> set (enumR as s k) \<Longrightarrow>
       length (to_bits (W as s) v) = W as s \<and> from_bits (to_bits (W as s) v) = v"
  and correctness_short':
    "\<And>as s.
     accepts' M' (x0 as s)
   = Coverage_TM.good x0 from_bits kk as s ((!) (x0 as s)) ((!) (x0 as s))"
  and read0_after_enc0':
    "\<And>as s.
       image (\<lambda>t. nat (head0' (conf' M' (enc as s kk) t)))
             {..< steps' M' (enc as s kk)}
     \<subseteq> { length (enc0 as s)
        ..< length (enc0 as s) + length (padL as s kk) + length (padR as s kk) }"
begin

(* Give the names Coverage_TM expects *)
abbreviation M_CL where "M_CL \<equiv> M'"
abbreviation steps_CL where "steps_CL \<equiv> steps'"
abbreviation conf_CL  where "conf_CL  \<equiv> conf'"
abbreviation head0_CL where "head0_CL \<equiv> head0'"
abbreviation accepts_CL where "accepts_CL \<equiv> accepts'"
abbreviation stepf_CL where "stepf_CL \<equiv> stepf'"
abbreviation final_acc_CL where "final_acc_CL \<equiv> final_acc'"
abbreviation x0 where
  "x0 as s \<equiv> SubsetSum_Padded_Enc.enc enc0 to_bits as s kk"

interpretation CL: CL_as_DTM_Run_Sem
  M_CL steps_CL conf_CL head0_CL accepts_CL stepf_CL final_acc_CL
  by (unfold_locales;
      (fact step_sem' steps_stable_raw' accepts_sem' conf0_same')?)

interpretation Cov: Coverage_TM
  steps_CL conf_CL head0_CL accepts_CL
  M_CL stepf_CL final_acc_CL
  enc0 to_bits from_bits kk
proof (unfold_locales)

  (* 1) Bits round-trip *)
  show
    "\<And>as s k v.
       v \<in> set (enumL as s k) \<union> set (enumR as s k) \<Longrightarrow>
       length (to_bits (W as s) v) = W as s \<and>
       from_bits (to_bits (W as s) v) = v"
    by (rule bits_roundtrip')

  (* 2) Acceptance equals the locale’s “good” (let Isabelle instantiate ?good) *)
  have corr0:
  "\<And>as s.
     accepts_CL M_CL (SubsetSum_Padded_Enc.enc enc0 to_bits as s kk)
   = Coverage_TM.good
       (\<lambda>as s. SubsetSum_Padded_Enc.enc enc0 to_bits as s kk)
       from_bits kk
       as s
       ((!) (SubsetSum_Padded_Enc.enc enc0 to_bits as s kk))
       ((!) (SubsetSum_Padded_Enc.enc enc0 to_bits as s kk))"
  using correctness_short' Coverage_TM.good_def
  by meson

  show
    "\<And>as s good.
       accepts_CL M_CL (SubsetSum_Padded_Enc.enc enc0 to_bits as s kk)
     = good as s
         ((!) (SubsetSum_Padded_Enc.enc enc0 to_bits as s kk))
         ((!) (SubsetSum_Padded_Enc.enc enc0 to_bits as s kk))"
    by (rule corr0)

  (* 3) Read window confinement *)
show
  "\<And>as s.
     CL.Base.read0 M_CL (x0 as s)
   \<subseteq> { length (enc0 as s)
      ..< length (enc0 as s)
         + length (SubsetSum_Padded_Enc.padL to_bits as s kk)
         + length (SubsetSum_Padded_Enc.padR to_bits as s kk) }"
proof -
  fix as s
  have read0_eq:
    "CL.Base.read0 M_CL (x0 as s)
     = (\<lambda>t. nat (head0_CL (conf_CL M_CL (x0 as s) t)))
         ` {..< steps_CL M_CL (x0 as s)}"
    unfolding DTM_Run.read0_def by simp
    (* If that line errors, replace DTM_Run.read0_def with the one your image has:
       try: CL.Base.read0_def   or   DTM_Run.Base.read0_def   or   read0_def.
       Use:  find_theorems name:read0_def   to discover the exact name. *)
  also have
    "(\<lambda>t. nat (head0_CL (conf_CL M_CL (x0 as s) t)))
       ` {..< steps_CL M_CL (x0 as s)}
     \<subseteq> { length (enc0 as s)
        ..< length (enc0 as s)
           + length (SubsetSum_Padded_Enc.padL to_bits as s kk)
           + length (SubsetSum_Padded_Enc.padR to_bits as s kk) }"
    by (rule read0_after_enc0')
  finally show
    "CL.Base.read0 M_CL (x0 as s)
     \<subseteq> { length (enc0 as s)
        ..< length (enc0 as s)
           + length (SubsetSum_Padded_Enc.padL to_bits as s kk)
           + length (SubsetSum_Padded_Enc.padR to_bits as s kk) }" .
  qed
qed
end
end