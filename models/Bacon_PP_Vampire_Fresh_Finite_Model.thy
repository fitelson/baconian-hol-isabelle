theory Bacon_PP_Vampire_Fresh_Finite_Model
  imports Main
begin

section \<open>Isabelle certificate for Vampire's finite Goodman model\<close>

text \<open>
  This theory checks the concrete interpretation printed by Vampire for
  \<open>fresh_attack/goodman_pp_refutation_finite.tff.in\<close>.  The four carriers
  have respectively two worlds, three propositions, five unary propositional
  operators, and two predicates of unary propositional operators.

  Each named lemma below certifies the TFF axiom with the corresponding name.
  The final theorem packages all twenty-five substantive axioms and records
  that the conjecture \<open>$false\<close> is false in the interpretation.  This is a
  certificate for the displayed finite first-order fragment.  It is not, by
  itself, a model of the full schematic theory in Goodman's question.

  In particular, the TFF file makes application world-indexed:
  \<open>app_p(W,X,P)\<close> and \<open>app_o(W,H,X)\<close> may return different propositions
  at different worlds.  Bacon's and Goodman's object language instead has
  unworlded application: one application term denotes one proposition, whose
  truth value may then vary by world.  The present model exploits this
  difference.  For example, applying \<open>pure_p\<close> to \<open>FP3\<close> returns \<open>FP2\<close>
  at \<open>FW1\<close> but \<open>FP3\<close> at \<open>FW2\<close>.  Thus the certificate establishes
  satisfiability of the TFF approximation, not of its intended object-language
  reading.
\<close>

datatype fresh_world = FW1 | FW2
datatype fresh_prop = FP1 | FP2 | FP3
datatype fresh_op1 = FO11 | FO12 | FO13 | FO14 | FO15
datatype fresh_op2 = FO21 | FO22

lemma fresh_world_forall [simp]:
  "(\<forall>W :: fresh_world. P W) \<longleftrightarrow> P FW1 \<and> P FW2"
proof
  assume "\<forall>W :: fresh_world. P W"
  then show "P FW1 \<and> P FW2"
    by simp
next
  assume "P FW1 \<and> P FW2"
  then show "\<forall>W :: fresh_world. P W"
    by (metis fresh_world.exhaust)
qed

lemma fresh_prop_forall [simp]:
  "(\<forall>P :: fresh_prop. Q P) \<longleftrightarrow>
    Q FP1 \<and> Q FP2 \<and> Q FP3"
proof
  assume "\<forall>P :: fresh_prop. Q P"
  then show "Q FP1 \<and> Q FP2 \<and> Q FP3"
    by simp
next
  assume "Q FP1 \<and> Q FP2 \<and> Q FP3"
  then show "\<forall>P :: fresh_prop. Q P"
    by (metis fresh_prop.exhaust)
qed

lemma fresh_op1_forall [simp]:
  "(\<forall>X :: fresh_op1. Q X) \<longleftrightarrow>
    Q FO11 \<and> Q FO12 \<and> Q FO13 \<and> Q FO14 \<and> Q FO15"
proof
  assume "\<forall>X :: fresh_op1. Q X"
  then show "Q FO11 \<and> Q FO12 \<and> Q FO13 \<and> Q FO14 \<and> Q FO15"
    by simp
next
  assume "Q FO11 \<and> Q FO12 \<and> Q FO13 \<and> Q FO14 \<and> Q FO15"
  then show "\<forall>X :: fresh_op1. Q X"
    by (metis fresh_op1.exhaust)
qed

lemma fresh_op2_forall [simp]:
  "(\<forall>H :: fresh_op2. Q H) \<longleftrightarrow> Q FO21 \<and> Q FO22"
proof
  assume "\<forall>H :: fresh_op2. Q H"
  then show "Q FO21 \<and> Q FO22"
    by simp
next
  assume "Q FO21 \<and> Q FO22"
  then show "\<forall>H :: fresh_op2. Q H"
    by (metis fresh_op2.exhaust)
qed

fun fresh_app_p ::
    "fresh_world \<Rightarrow> fresh_op1 \<Rightarrow> fresh_prop \<Rightarrow> fresh_prop"
where
  "fresh_app_p FW1 FO11 FP1 = FP1"
| "fresh_app_p FW1 FO11 FP2 = FP1"
| "fresh_app_p FW1 FO11 FP3 = FP2"
| "fresh_app_p FW1 FO12 FP1 = FP2"
| "fresh_app_p FW1 FO12 FP2 = FP2"
| "fresh_app_p FW1 FO12 FP3 = FP3"
| "fresh_app_p FW1 FO13 FP1 = FP1"
| "fresh_app_p FW1 FO13 FP2 = FP2"
| "fresh_app_p FW1 FO13 FP3 = FP3"
| "fresh_app_p FW1 FO14 FP1 = FP2"
| "fresh_app_p FW1 FO14 FP2 = FP1"
| "fresh_app_p FW1 FO14 FP3 = FP2"
| "fresh_app_p FW1 FO15 FP1 = FP1"
| "fresh_app_p FW1 FO15 FP2 = FP2"
| "fresh_app_p FW1 FO15 FP3 = FP2"
| "fresh_app_p FW2 FO11 FP1 = FP1"
| "fresh_app_p FW2 FO11 FP2 = FP1"
| "fresh_app_p FW2 FO11 FP3 = FP3"
| "fresh_app_p FW2 FO12 FP1 = FP2"
| "fresh_app_p FW2 FO12 FP2 = FP2"
| "fresh_app_p FW2 FO12 FP3 = FP1"
| "fresh_app_p FW2 FO13 FP1 = FP1"
| "fresh_app_p FW2 FO13 FP2 = FP2"
| "fresh_app_p FW2 FO13 FP3 = FP3"
| "fresh_app_p FW2 FO14 FP1 = FP2"
| "fresh_app_p FW2 FO14 FP2 = FP1"
| "fresh_app_p FW2 FO14 FP3 = FP1"
| "fresh_app_p FW2 FO15 FP1 = FP1"
| "fresh_app_p FW2 FO15 FP2 = FP2"
| "fresh_app_p FW2 FO15 FP3 = FP3"

fun fresh_app_o ::
    "fresh_world \<Rightarrow> fresh_op2 \<Rightarrow> fresh_op1 \<Rightarrow> fresh_prop"
where
  "fresh_app_o FW1 FO21 FO11 = FP3"
| "fresh_app_o FW1 FO21 FO12 = FP2"
| "fresh_app_o FW1 FO21 FO13 = FP3"
| "fresh_app_o FW1 FO21 FO14 = FP3"
| "fresh_app_o FW1 FO21 FO15 = FP3"
| "fresh_app_o FW1 FO22 FO11 = FP2"
| "fresh_app_o FW1 FO22 FO12 = FP2"
| "fresh_app_o FW1 FO22 FO13 = FP2"
| "fresh_app_o FW1 FO22 FO14 = FP2"
| "fresh_app_o FW1 FO22 FO15 = FP2"
| "fresh_app_o FW2 FO21 FO11 = FP1"
| "fresh_app_o FW2 FO21 FO12 = FP2"
| "fresh_app_o FW2 FO21 FO13 = FP1"
| "fresh_app_o FW2 FO21 FO14 = FP1"
| "fresh_app_o FW2 FO21 FO15 = FP1"
| "fresh_app_o FW2 FO22 FO11 = FP2"
| "fresh_app_o FW2 FO22 FO12 = FP2"
| "fresh_app_o FW2 FO22 FO13 = FP2"
| "fresh_app_o FW2 FO22 FO14 = FP2"
| "fresh_app_o FW2 FO22 FO15 = FP2"

fun fresh_holds :: "fresh_world \<Rightarrow> fresh_prop \<Rightarrow> bool" where
  "fresh_holds FW1 FP1 = True"
| "fresh_holds FW1 FP2 = False"
| "fresh_holds FW1 FP3 = True"
| "fresh_holds FW2 FP1 = True"
| "fresh_holds FW2 FP2 = False"
| "fresh_holds FW2 FP3 = False"

fun fresh_is_pure_p :: "fresh_world \<Rightarrow> fresh_prop \<Rightarrow> bool" where
  "fresh_is_pure_p W FP1 = True"
| "fresh_is_pure_p W FP2 = True"
| "fresh_is_pure_p W FP3 = False"

fun fresh_is_pure_o :: "fresh_world \<Rightarrow> fresh_op1 \<Rightarrow> bool" where
  "fresh_is_pure_o W FO11 = True"
| "fresh_is_pure_o W FO12 = False"
| "fresh_is_pure_o W FO13 = True"
| "fresh_is_pure_o W FO14 = True"
| "fresh_is_pure_o W FO15 = True"

fun fresh_is_fun_p :: "fresh_world \<Rightarrow> fresh_prop \<Rightarrow> bool" where
  "fresh_is_fun_p W FP1 = False"
| "fresh_is_fun_p W FP2 = False"
| "fresh_is_fun_p W FP3 = True"

fun fresh_is_fun_o :: "fresh_world \<Rightarrow> fresh_op1 \<Rightarrow> bool" where
  "fresh_is_fun_o W X = False"

fun fresh_is_fun_oo :: "fresh_world \<Rightarrow> fresh_op2 \<Rightarrow> bool" where
  "fresh_is_fun_oo W H = False"

abbreviation fresh_pure_p :: fresh_op1 where "fresh_pure_p \<equiv> FO11"
abbreviation fresh_pure_o :: fresh_op2 where "fresh_pure_o \<equiv> FO21"
abbreviation fresh_fun_p :: fresh_op1 where "fresh_fun_p \<equiv> FO12"
abbreviation fresh_fun_o :: fresh_op2 where "fresh_fun_o \<equiv> FO22"
abbreviation fresh_top_p :: fresh_prop where "fresh_top_p \<equiv> FP1"
abbreviation fresh_bot_p :: fresh_prop where "fresh_bot_p \<equiv> FP2"
abbreviation fresh_id_o :: fresh_op1 where "fresh_id_o \<equiv> FO13"
abbreviation fresh_not_o :: fresh_op1 where "fresh_not_o \<equiv> FO14"
abbreviation fresh_box_o :: fresh_op1 where "fresh_box_o \<equiv> FO15"

subsection \<open>Classifier objects and logical objects\<close>

lemma fresh_pure_prop_definition:
  "\<forall>W P. fresh_is_pure_p W P
    \<longleftrightarrow> fresh_holds W (fresh_app_p W fresh_pure_p P)"
  by simp

lemma fresh_pure_op_definition:
  "\<forall>W X. fresh_is_pure_o W X
    \<longleftrightarrow> fresh_holds W (fresh_app_o W fresh_pure_o X)"
  by simp

lemma fresh_fun_prop_definition:
  "\<forall>W P. fresh_is_fun_p W P
    \<longleftrightarrow> fresh_holds W (fresh_app_p W fresh_fun_p P)"
  by simp

lemma fresh_fun_op_definition:
  "\<forall>W X. fresh_is_fun_o W X
    \<longleftrightarrow> fresh_holds W (fresh_app_o W fresh_fun_o X)"
  by simp

lemma fresh_top_truth:
  "\<forall>W. fresh_holds W fresh_top_p"
  by simp

lemma fresh_bottom_falsity:
  "\<forall>W. \<not> fresh_holds W fresh_bot_p"
  by simp

lemma fresh_identity_application:
  "\<forall>W P. fresh_app_p W fresh_id_o P = P"
  by simp

lemma fresh_negation_truth:
  "\<forall>W P. fresh_holds W (fresh_app_p W fresh_not_o P)
    \<longleftrightarrow> \<not> fresh_holds W P"
  by simp

lemma fresh_box_truth:
  "\<forall>W P. fresh_holds W (fresh_app_p W fresh_box_o P)
    \<longleftrightarrow> (\<forall>V. fresh_holds V P)"
  by simp

subsection \<open>Purity, fundamentality, and QLN\<close>

lemma fresh_pure_top:
  "\<forall>W. fresh_is_pure_p W fresh_top_p"
  by simp

lemma fresh_pure_bottom:
  "\<forall>W. fresh_is_pure_p W fresh_bot_p"
  by simp

lemma fresh_pure_identity:
  "\<forall>W. fresh_is_pure_o W fresh_id_o"
  by simp

lemma fresh_pure_negation:
  "\<forall>W. fresh_is_pure_o W fresh_not_o"
  by simp

lemma fresh_pure_box:
  "\<forall>W. fresh_is_pure_o W fresh_box_o"
  by simp

lemma fresh_pure_application_prop:
  "\<forall>W X P. (fresh_is_pure_o W X \<and> fresh_is_pure_p W P)
    \<longrightarrow> fresh_is_pure_p W (fresh_app_p W X P)"
  by simp

lemma fresh_unique_fundamental_proposition:
  "\<forall>W. \<exists>P. fresh_is_fun_p W P
    \<and> (\<forall>Q. fresh_is_fun_p W Q \<longrightarrow> Q = P)"
  by (intro allI; rule exI[of _ FP3]; simp)

lemma fresh_no_fundamental_op1:
  "\<forall>W X. \<not> fresh_is_fun_o W X"
  by simp

lemma fresh_no_fundamental_op2:
  "\<forall>W H. \<not> fresh_is_fun_oo W H"
  by simp

lemma fresh_zeroary_recombination:
  "\<forall>W P. (fresh_is_pure_p W P \<and> (\<forall>V. fresh_holds V P))
    \<longrightarrow> fresh_holds W P"
  by simp

lemma fresh_zeroary_exhaustion:
  "\<forall>W P. (fresh_is_pure_p W P \<and> fresh_holds W P)
    \<longrightarrow> (\<forall>V. fresh_holds V P)"
  by simp

lemma fresh_unary_recombination:
  "\<forall>W X P.
    (fresh_is_pure_o W X
      \<and> fresh_is_fun_p W P
      \<and> (\<forall>V. fresh_holds V (fresh_app_p V X P)))
    \<longrightarrow> (\<forall>Q. fresh_holds W (fresh_app_p W X Q))"
  by simp

lemma fresh_unary_exhaustion:
  "\<forall>W X P.
    (fresh_is_pure_o W X
      \<and> fresh_is_fun_p W P
      \<and> (\<forall>Q. fresh_holds W (fresh_app_p W X Q)))
    \<longrightarrow> (\<forall>V. fresh_holds V (fresh_app_p V X P))"
  by simp

subsection \<open>Modalized Functionality and PP\<close>

lemma fresh_modalized_functionality_op1:
  "\<forall>(W :: fresh_world) X Y.
    ((\<forall>V P. fresh_app_p V X P = fresh_app_p V Y P)
      \<longrightarrow> X = Y)"
  by simp

lemma fresh_modalized_functionality_op2:
  "\<forall>(W :: fresh_world) H K.
    ((\<forall>V X. fresh_app_o V H X = fresh_app_o V K X)
      \<longrightarrow> H = K)"
  by simp

lemma fresh_goodman_PP:
  "\<forall>W. fresh_is_pure_o W fresh_pure_p"
  by simp

subsection \<open>The complete finite certificate\<close>

definition fresh_goodman_tff_axioms_hold :: bool where
  "fresh_goodman_tff_axioms_hold \<longleftrightarrow>
      (\<forall>W P. fresh_is_pure_p W P
        \<longleftrightarrow> fresh_holds W (fresh_app_p W fresh_pure_p P))
    \<and> (\<forall>W X. fresh_is_pure_o W X
        \<longleftrightarrow> fresh_holds W (fresh_app_o W fresh_pure_o X))
    \<and> (\<forall>W P. fresh_is_fun_p W P
        \<longleftrightarrow> fresh_holds W (fresh_app_p W fresh_fun_p P))
    \<and> (\<forall>W X. fresh_is_fun_o W X
        \<longleftrightarrow> fresh_holds W (fresh_app_o W fresh_fun_o X))
    \<and> (\<forall>W. fresh_holds W fresh_top_p)
    \<and> (\<forall>W. \<not> fresh_holds W fresh_bot_p)
    \<and> (\<forall>W P. fresh_app_p W fresh_id_o P = P)
    \<and> (\<forall>W P. fresh_holds W (fresh_app_p W fresh_not_o P)
        \<longleftrightarrow> \<not> fresh_holds W P)
    \<and> (\<forall>W P. fresh_holds W (fresh_app_p W fresh_box_o P)
        \<longleftrightarrow> (\<forall>V. fresh_holds V P))
    \<and> (\<forall>W. fresh_is_pure_p W fresh_top_p)
    \<and> (\<forall>W. fresh_is_pure_p W fresh_bot_p)
    \<and> (\<forall>W. fresh_is_pure_o W fresh_id_o)
    \<and> (\<forall>W. fresh_is_pure_o W fresh_not_o)
    \<and> (\<forall>W. fresh_is_pure_o W fresh_box_o)
    \<and> (\<forall>W X P. (fresh_is_pure_o W X \<and> fresh_is_pure_p W P)
        \<longrightarrow> fresh_is_pure_p W (fresh_app_p W X P))
    \<and> (\<forall>W. \<exists>P. fresh_is_fun_p W P
        \<and> (\<forall>Q. fresh_is_fun_p W Q \<longrightarrow> Q = P))
    \<and> (\<forall>W X. \<not> fresh_is_fun_o W X)
    \<and> (\<forall>W H. \<not> fresh_is_fun_oo W H)
    \<and> (\<forall>W P. (fresh_is_pure_p W P \<and> (\<forall>V. fresh_holds V P))
        \<longrightarrow> fresh_holds W P)
    \<and> (\<forall>W P. (fresh_is_pure_p W P \<and> fresh_holds W P)
        \<longrightarrow> (\<forall>V. fresh_holds V P))
    \<and> (\<forall>W X P.
        (fresh_is_pure_o W X
          \<and> fresh_is_fun_p W P
          \<and> (\<forall>V. fresh_holds V (fresh_app_p V X P)))
        \<longrightarrow> (\<forall>Q. fresh_holds W (fresh_app_p W X Q)))
    \<and> (\<forall>W X P.
        (fresh_is_pure_o W X
          \<and> fresh_is_fun_p W P
          \<and> (\<forall>Q. fresh_holds W (fresh_app_p W X Q)))
        \<longrightarrow> (\<forall>V. fresh_holds V (fresh_app_p V X P)))
    \<and> (\<forall>(W :: fresh_world) X Y.
        ((\<forall>V P. fresh_app_p V X P = fresh_app_p V Y P)
          \<longrightarrow> X = Y))
    \<and> (\<forall>(W :: fresh_world) H K.
        ((\<forall>V X. fresh_app_o V H X = fresh_app_o V K X)
          \<longrightarrow> H = K))
    \<and> (\<forall>W. fresh_is_pure_o W fresh_pure_p)"

theorem fresh_goodman_tff_model_certificate:
  fresh_goodman_tff_axioms_hold
  unfolding fresh_goodman_tff_axioms_hold_def
  using fresh_pure_prop_definition fresh_pure_op_definition
    fresh_fun_prop_definition fresh_fun_op_definition
    fresh_top_truth fresh_bottom_falsity fresh_identity_application
    fresh_negation_truth fresh_box_truth
    fresh_pure_top fresh_pure_bottom fresh_pure_identity
    fresh_pure_negation fresh_pure_box fresh_pure_application_prop
    fresh_unique_fundamental_proposition
    fresh_no_fundamental_op1 fresh_no_fundamental_op2
    fresh_zeroary_recombination fresh_zeroary_exhaustion
    fresh_unary_recombination fresh_unary_exhaustion
    fresh_modalized_functionality_op1
    fresh_modalized_functionality_op2 fresh_goodman_PP
  by blast

theorem fresh_goodman_tff_countermodel_certificate:
  "fresh_goodman_tff_axioms_hold \<and> \<not> False"
  using fresh_goodman_tff_model_certificate by simp

end
