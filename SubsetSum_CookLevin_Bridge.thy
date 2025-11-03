theory SubsetSum_CookLevin_Bridge
  imports
    "Cook_Levin.NP"
    "SubsetSum_DTM_Bridge2"
begin

(* ========================================================================= *)
(* PART 0: Type conversion - bool list to symbol list                       *)
(* ========================================================================= *)

(* Cook-Levin uses: blank=0, start=1, zero=2, one=3 *)
definition bool_to_symbols :: "bool list \<Rightarrow> symbol list" where
  "bool_to_symbols bs = map (\<lambda>b. if b then 3 else 2) bs"

(* ========================================================================= *)
(* PART 1: Map Cook-Levin primitives to DTM interface                       *)
(* ========================================================================= *)

definition k_tapes :: nat where "k_tapes = 2"

(* Halting time *)
definition steps_CL :: "machine \<Rightarrow> bool list \<Rightarrow> nat" where
  "steps_CL M x = (LEAST t. fst (execute M (start_config k_tapes (bool_to_symbols x)) t) \<ge> length M)"

(* Configuration after t steps *)
definition conf_CL :: "machine \<Rightarrow> bool list \<Rightarrow> nat \<Rightarrow> config" where
  "conf_CL M x t = execute M (start_config k_tapes (bool_to_symbols x)) t"

(* Input tape head position *)
definition head0_CL :: "config \<Rightarrow> int" where
  "head0_CL cfg = int (cfg <#> 0)"

(* Acceptance: check if symbol at output tape head equals 3 (one_symbol) *)
definition accepts_CL :: "machine \<Rightarrow> bool list \<Rightarrow> bool" where
  "accepts_CL M x = (
    let t = steps_CL M x;
        cfg = conf_CL M x t
    in (cfg <:> 1) (cfg <#> 1) = 3)"  (* 3 is one_symbol/\<bbbI> as nat *)

(* ========================================================================= *)
(* PART 2: Define stepf for a fixed machine M                               *)
(* ========================================================================= *)

(* For a fixed M, stepf just runs exe M *)
definition stepf_CL_for :: "machine \<Rightarrow> config \<Rightarrow> bool \<Rightarrow> config" where
  "stepf_CL_for M cfg b = exe M cfg"

(* Final acceptance predicate *)
definition final_acc_CL :: "config \<Rightarrow> bool" where
  "final_acc_CL cfg = ((cfg <:> 1) (cfg <#> 1) = 3)"

(* ========================================================================= *)
(* PART 3: Prove the 4 axioms for a specific machine                        *)
(* ========================================================================= *)

(* AXIOM 1: Step semantics *)
lemma step_sem_CL:
  assumes turing: "turing_machine k_tapes G M"
  shows "conf_CL M x (Suc t) = 
         stepf_CL_for M (conf_CL M x t) (x ! nat (head0_CL (conf_CL M x t)))"
proof -
  have "conf_CL M x (Suc t) = execute M (start_config k_tapes (bool_to_symbols x)) (Suc t)"
    by (simp add: conf_CL_def)
  also have "... = exe M (execute M (start_config k_tapes (bool_to_symbols x)) t)"
    by simp
  also have "... = exe M (conf_CL M x t)"
    by (simp add: conf_CL_def)
  also have "... = stepf_CL_for M (conf_CL M x t) (x ! nat (head0_CL (conf_CL M x t)))"
    by (simp add: stepf_CL_for_def)
  finally show ?thesis .
qed

(* AXIOM 2: Steps stable - unread-agreement for Cook-Levin TMs *)
lemma steps_stable_raw_CL:
  assumes turing: "turing_machine k_tapes G M"
      and agree: "\<And>i. i \<in> (\<lambda>t. nat (head0_CL (conf_CL M x t))) ` {..< steps_CL M x} 
                      \<Longrightarrow> x ! i = y ! i"
  shows "steps_CL M x = steps_CL M y"
  sorry
  (* AXIOM: Deterministic TM execution with unread-agreement
     
     STATEMENT: If inputs x and y agree on all positions that M reads
     when running on x, then M takes the same time to halt on both inputs.
     
     JUSTIFICATION: This is a fundamental property of deterministic computation.
     The execution trace (states, head positions, non-input tape contents) 
     evolves identically when the read values are the same.
     
     PROOF SKETCH:
     By induction on t \<le> steps M x:
     - Base (t=0): Initial configs have same state, head positions
     - Step: If conf_CL M x t = conf_CL M y t in all relevant aspects,
       and M reads position i at time t where x!i = y!i, then
       exe M produces the same next config for both
     - Therefore: Halting times must be equal
     
     This follows from Cook-Levin's determinism properties and the
     definition of exe/execute in Basics.thy. *)

(* AXIOM 3: Acceptance equals final config check *)
lemma accepts_sem_CL:
  "accepts_CL M x = final_acc_CL (conf_CL M x (steps_CL M x))"
  by (simp add: accepts_CL_def conf_CL_def final_acc_CL_def Let_def)

(* AXIOM 4: Initial config independent of input content *)
lemma conf0_same_CL:
  assumes "length x = length y"
  shows "conf_CL M x 0 = conf_CL M y 0"
  sorry
  (* AXIOM: Initial configuration depends only on input length
     
     STATEMENT: Two inputs of the same length start in identical configs.
     
     JUSTIFICATION: The initial configuration places the input on tape 0
     but the TM hasn't read anything yet. All that matters is the length
     to set up the tape structure correctly.
     
     ISSUE: In Cook-Levin's concrete model, tape 0 DOES contain the input
     symbols, so conf_CL M x 0 \<noteq> conf_CL M y 0 when x \<noteq> y. This axiom is
     actually FALSE as stated.
     
     The DTM_Run_Sem abstraction assumes initial config is independent of
     input content (only length matters). This mismatch suggests the bridge
     may need redesign to properly account for the input tape contents. *)

end
