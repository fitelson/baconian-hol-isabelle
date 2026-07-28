theory Bacon_PP_Vampire_Unworlded_Finite_Model
  imports Main
begin

section \<open>Certificate for Vampire's unworlded finite Goodman model\<close>

text \<open>
  This theory checks the concrete interpretation printed by Vampire for
  \<open>theories/goodman/cevplus/goodman_pp_refutation_finite_unworlded.tff.in\<close>.  Its four
  carriers contain two worlds, four propositions, five unary propositional
  operators, and two predicates of unary propositional operators.

  Unlike the earlier finite approximation, application is unworlded:
  \<open>unw_app_p X P\<close> and \<open>unw_app_o H X\<close> each denote one proposition.
  Only the truth of that proposition may vary by world.  Each named lemma below
  certifies the TFF axiom with the corresponding name, and the final theorem
  packages all twenty-five substantive axioms.

  The certificate has two exact limits.  First, the finite TFF clause for
  \<open>box_o\<close> identifies necessity with truth at every represented world.  This
  is only a finite surrogate for Bacon and Dorr's interpretation
  \<open>Box A = (A = top)\<close>; the TFF language does not represent that identity
  condition on proposition objects.  Second, the benchmark does not encode the full
  all-type CEV semantics, the complete stock of closed logical terms, or every
  type instance of the Purity schemas.  Thus this is a model of the displayed
  finite first-order fragment, not a model of the full theory in Goodman's
  consistency question.
\<close>

datatype unw_world = UW1 | UW2
datatype unw_prop = UP1 | UP2 | UP3 | UP4
datatype unw_op1 = UO11 | UO12 | UO13 | UO14 | UO15
datatype unw_op2 = UO21 | UO22

lemma unw_world_forall [simp]:
  "(\<forall>W :: unw_world. P W) \<longleftrightarrow> P UW1 \<and> P UW2"
  by (metis unw_world.exhaust)

lemma unw_prop_forall [simp]:
  "(\<forall>P :: unw_prop. Q P) \<longleftrightarrow>
    Q UP1 \<and> Q UP2 \<and> Q UP3 \<and> Q UP4"
  by (metis unw_prop.exhaust)

lemma unw_op1_forall [simp]:
  "(\<forall>X :: unw_op1. Q X) \<longleftrightarrow>
    Q UO11 \<and> Q UO12 \<and> Q UO13 \<and> Q UO14 \<and> Q UO15"
  by (metis unw_op1.exhaust)

lemma unw_op2_forall [simp]:
  "(\<forall>H :: unw_op2. Q H) \<longleftrightarrow> Q UO21 \<and> Q UO22"
  by (metis unw_op2.exhaust)

fun unw_app_p :: "unw_op1 \<Rightarrow> unw_prop \<Rightarrow> unw_prop" where
  "unw_app_p UO11 UP1 = UP1"
| "unw_app_p UO11 UP2 = UP1"
| "unw_app_p UO11 UP3 = UP2"
| "unw_app_p UO11 UP4 = UP2"
| "unw_app_p UO12 UP1 = UP2"
| "unw_app_p UO12 UP2 = UP2"
| "unw_app_p UO12 UP3 = UP4"
| "unw_app_p UO12 UP4 = UP3"
| "unw_app_p UO13 UP1 = UP1"
| "unw_app_p UO13 UP2 = UP2"
| "unw_app_p UO13 UP3 = UP3"
| "unw_app_p UO13 UP4 = UP4"
| "unw_app_p UO14 UP1 = UP2"
| "unw_app_p UO14 UP2 = UP1"
| "unw_app_p UO14 UP3 = UP4"
| "unw_app_p UO14 UP4 = UP3"
| "unw_app_p UO15 UP1 = UP1"
| "unw_app_p UO15 UP2 = UP2"
| "unw_app_p UO15 UP3 = UP2"
| "unw_app_p UO15 UP4 = UP2"

fun unw_app_o :: "unw_op2 \<Rightarrow> unw_op1 \<Rightarrow> unw_prop" where
  "unw_app_o UO21 UO11 = UP1"
| "unw_app_o UO21 UO12 = UP4"
| "unw_app_o UO21 UO13 = UP1"
| "unw_app_o UO21 UO14 = UP1"
| "unw_app_o UO21 UO15 = UP1"
| "unw_app_o UO22 UO11 = UP2"
| "unw_app_o UO22 UO12 = UP2"
| "unw_app_o UO22 UO13 = UP2"
| "unw_app_o UO22 UO14 = UP2"
| "unw_app_o UO22 UO15 = UP2"

fun unw_holds :: "unw_world \<Rightarrow> unw_prop \<Rightarrow> bool" where
  "unw_holds UW1 UP1 = True"
| "unw_holds UW1 UP2 = False"
| "unw_holds UW1 UP3 = False"
| "unw_holds UW1 UP4 = True"
| "unw_holds UW2 UP1 = True"
| "unw_holds UW2 UP2 = False"
| "unw_holds UW2 UP3 = True"
| "unw_holds UW2 UP4 = False"

definition unw_is_pure_p :: "unw_world \<Rightarrow> unw_prop \<Rightarrow> bool" where
  "unw_is_pure_p W P \<longleftrightarrow> unw_holds W (unw_app_p UO11 P)"

definition unw_is_pure_o :: "unw_world \<Rightarrow> unw_op1 \<Rightarrow> bool" where
  "unw_is_pure_o W X \<longleftrightarrow> unw_holds W (unw_app_o UO21 X)"

definition unw_is_fun_p :: "unw_world \<Rightarrow> unw_prop \<Rightarrow> bool" where
  "unw_is_fun_p W P \<longleftrightarrow> unw_holds W (unw_app_p UO12 P)"

definition unw_is_fun_o :: "unw_world \<Rightarrow> unw_op1 \<Rightarrow> bool" where
  "unw_is_fun_o W X \<longleftrightarrow> unw_holds W (unw_app_o UO22 X)"

definition unw_is_fun_oo :: "unw_world \<Rightarrow> unw_op2 \<Rightarrow> bool" where
  "unw_is_fun_oo W H \<longleftrightarrow> False"

abbreviation unw_pure_p :: unw_op1 where "unw_pure_p \<equiv> UO11"
abbreviation unw_pure_o :: unw_op2 where "unw_pure_o \<equiv> UO21"
abbreviation unw_fun_p :: unw_op1 where "unw_fun_p \<equiv> UO12"
abbreviation unw_fun_o :: unw_op2 where "unw_fun_o \<equiv> UO22"
abbreviation unw_top_p :: unw_prop where "unw_top_p \<equiv> UP1"
abbreviation unw_bot_p :: unw_prop where "unw_bot_p \<equiv> UP2"
abbreviation unw_id_o :: unw_op1 where "unw_id_o \<equiv> UO13"
abbreviation unw_not_o :: unw_op1 where "unw_not_o \<equiv> UO14"
abbreviation unw_box_o :: unw_op1 where "unw_box_o \<equiv> UO15"

subsection \<open>Classifier objects and logical objects\<close>

lemma unw_pure_prop_definition:
  "\<forall>W P. unw_is_pure_p W P
    \<longleftrightarrow> unw_holds W (unw_app_p unw_pure_p P)"
  by (simp add: unw_is_pure_p_def)

lemma unw_pure_op_definition:
  "\<forall>W X. unw_is_pure_o W X
    \<longleftrightarrow> unw_holds W (unw_app_o unw_pure_o X)"
  by (simp add: unw_is_pure_o_def)

lemma unw_fun_prop_definition:
  "\<forall>W P. unw_is_fun_p W P
    \<longleftrightarrow> unw_holds W (unw_app_p unw_fun_p P)"
  by (simp add: unw_is_fun_p_def)

lemma unw_fun_op_definition:
  "\<forall>W X. unw_is_fun_o W X
    \<longleftrightarrow> unw_holds W (unw_app_o unw_fun_o X)"
  by (simp add: unw_is_fun_o_def)

lemma unw_top_truth:
  "\<forall>W. unw_holds W unw_top_p"
  by simp

lemma unw_bottom_falsity:
  "\<forall>W. \<not> unw_holds W unw_bot_p"
  by simp

lemma unw_identity_application:
  "\<forall>P. unw_app_p unw_id_o P = P"
  by simp

lemma unw_negation_truth:
  "\<forall>W P. unw_holds W (unw_app_p unw_not_o P)
    \<longleftrightarrow> \<not> unw_holds W P"
  by simp

lemma unw_box_truth:
  "\<forall>W P. unw_holds W (unw_app_p unw_box_o P)
    \<longleftrightarrow> (\<forall>V. unw_holds V P)"
  by simp

subsection \<open>Purity, fundamentality, and QLN\<close>

lemma unw_pure_top:
  "\<forall>W. unw_is_pure_p W unw_top_p"
  by (simp add: unw_is_pure_p_def)

lemma unw_pure_bottom:
  "\<forall>W. unw_is_pure_p W unw_bot_p"
  by (simp add: unw_is_pure_p_def)

lemma unw_pure_identity:
  "\<forall>W. unw_is_pure_o W unw_id_o"
  by (simp add: unw_is_pure_o_def)

lemma unw_pure_negation:
  "\<forall>W. unw_is_pure_o W unw_not_o"
  by (simp add: unw_is_pure_o_def)

lemma unw_pure_box:
  "\<forall>W. unw_is_pure_o W unw_box_o"
  by (simp add: unw_is_pure_o_def)

lemma unw_pure_application_prop:
  "\<forall>W X P. (unw_is_pure_o W X \<and> unw_is_pure_p W P)
    \<longrightarrow> unw_is_pure_p W (unw_app_p X P)"
  by (simp add: unw_is_pure_o_def unw_is_pure_p_def)

lemma unw_unique_fundamental_proposition:
  "\<forall>W. \<exists>P. unw_is_fun_p W P
    \<and> (\<forall>Q. unw_is_fun_p W Q \<longrightarrow> Q = P)"
proof (intro allI)
  fix W
  show "\<exists>P. unw_is_fun_p W P
      \<and> (\<forall>Q. unw_is_fun_p W Q \<longrightarrow> Q = P)"
  proof (cases W)
    case UW1
    show ?thesis
      apply (rule exI[of _ UP3])
      using UW1
      apply (simp add: unw_is_fun_p_def)
      done
  next
    case UW2
    show ?thesis
      apply (rule exI[of _ UP4])
      using UW2
      apply (simp add: unw_is_fun_p_def)
      done
  qed
qed

lemma unw_no_fundamental_op1:
  "\<forall>W X. \<not> unw_is_fun_o W X"
  by (simp add: unw_is_fun_o_def)

lemma unw_no_fundamental_op2:
  "\<forall>W H. \<not> unw_is_fun_oo W H"
  by (simp add: unw_is_fun_oo_def)

lemma unw_zeroary_recombination:
  "\<forall>W P. (unw_is_pure_p W P \<and> (\<forall>V. unw_holds V P))
    \<longrightarrow> unw_holds W P"
  by (simp add: unw_is_pure_p_def)

lemma unw_zeroary_exhaustion:
  "\<forall>W P. (unw_is_pure_p W P \<and> unw_holds W P)
    \<longrightarrow> (\<forall>V. unw_holds V P)"
  by (simp add: unw_is_pure_p_def)

lemma unw_unary_recombination:
  "\<forall>W X P.
    (unw_is_pure_o W X
      \<and> unw_is_fun_p W P
      \<and> (\<forall>V. unw_holds V (unw_app_p X P)))
    \<longrightarrow> (\<forall>Q. unw_holds W (unw_app_p X Q))"
  by (simp add: unw_is_pure_o_def unw_is_fun_p_def)

lemma unw_unary_exhaustion:
  "\<forall>W X P.
    (unw_is_pure_o W X
      \<and> unw_is_fun_p W P
      \<and> (\<forall>Q. unw_holds W (unw_app_p X Q)))
    \<longrightarrow> (\<forall>V. unw_holds V (unw_app_p X P))"
  by (simp add: unw_is_pure_o_def unw_is_fun_p_def)

subsection \<open>Modalized Functionality and PP\<close>

lemma unw_modalized_functionality_op1:
  "\<forall>(W :: unw_world) X Y.
    ((\<forall>(V :: unw_world) P. unw_app_p X P = unw_app_p Y P)
      \<longrightarrow> X = Y)"
  by simp

lemma unw_modalized_functionality_op2:
  "\<forall>(W :: unw_world) H K.
    ((\<forall>(V :: unw_world) X. unw_app_o H X = unw_app_o K X)
      \<longrightarrow> H = K)"
  by simp

lemma unw_goodman_PP:
  "\<forall>W. unw_is_pure_o W unw_pure_p"
  by (simp add: unw_is_pure_o_def)

subsection \<open>The complete finite certificate\<close>

definition unw_goodman_tff_axioms_hold :: bool where
  "unw_goodman_tff_axioms_hold \<longleftrightarrow>
      (\<forall>W P. unw_is_pure_p W P
        \<longleftrightarrow> unw_holds W (unw_app_p unw_pure_p P))
    \<and> (\<forall>W X. unw_is_pure_o W X
        \<longleftrightarrow> unw_holds W (unw_app_o unw_pure_o X))
    \<and> (\<forall>W P. unw_is_fun_p W P
        \<longleftrightarrow> unw_holds W (unw_app_p unw_fun_p P))
    \<and> (\<forall>W X. unw_is_fun_o W X
        \<longleftrightarrow> unw_holds W (unw_app_o unw_fun_o X))
    \<and> (\<forall>W. unw_holds W unw_top_p)
    \<and> (\<forall>W. \<not> unw_holds W unw_bot_p)
    \<and> (\<forall>P. unw_app_p unw_id_o P = P)
    \<and> (\<forall>W P. unw_holds W (unw_app_p unw_not_o P)
        \<longleftrightarrow> \<not> unw_holds W P)
    \<and> (\<forall>W P. unw_holds W (unw_app_p unw_box_o P)
        \<longleftrightarrow> (\<forall>V. unw_holds V P))
    \<and> (\<forall>W. unw_is_pure_p W unw_top_p)
    \<and> (\<forall>W. unw_is_pure_p W unw_bot_p)
    \<and> (\<forall>W. unw_is_pure_o W unw_id_o)
    \<and> (\<forall>W. unw_is_pure_o W unw_not_o)
    \<and> (\<forall>W. unw_is_pure_o W unw_box_o)
    \<and> (\<forall>W X P. (unw_is_pure_o W X \<and> unw_is_pure_p W P)
        \<longrightarrow> unw_is_pure_p W (unw_app_p X P))
    \<and> (\<forall>W. \<exists>P. unw_is_fun_p W P
        \<and> (\<forall>Q. unw_is_fun_p W Q \<longrightarrow> Q = P))
    \<and> (\<forall>W X. \<not> unw_is_fun_o W X)
    \<and> (\<forall>W H. \<not> unw_is_fun_oo W H)
    \<and> (\<forall>W P. (unw_is_pure_p W P \<and> (\<forall>V. unw_holds V P))
        \<longrightarrow> unw_holds W P)
    \<and> (\<forall>W P. (unw_is_pure_p W P \<and> unw_holds W P)
        \<longrightarrow> (\<forall>V. unw_holds V P))
    \<and> (\<forall>W X P.
        (unw_is_pure_o W X
          \<and> unw_is_fun_p W P
          \<and> (\<forall>V. unw_holds V (unw_app_p X P)))
        \<longrightarrow> (\<forall>Q. unw_holds W (unw_app_p X Q)))
    \<and> (\<forall>W X P.
        (unw_is_pure_o W X
          \<and> unw_is_fun_p W P
          \<and> (\<forall>Q. unw_holds W (unw_app_p X Q)))
        \<longrightarrow> (\<forall>V. unw_holds V (unw_app_p X P)))
    \<and> (\<forall>(W :: unw_world) X Y.
        ((\<forall>(V :: unw_world) P. unw_app_p X P = unw_app_p Y P)
          \<longrightarrow> X = Y))
    \<and> (\<forall>(W :: unw_world) H K.
        ((\<forall>(V :: unw_world) X. unw_app_o H X = unw_app_o K X)
          \<longrightarrow> H = K))
    \<and> (\<forall>W. unw_is_pure_o W unw_pure_p)"

theorem unw_goodman_tff_model_certificate:
  unw_goodman_tff_axioms_hold
  unfolding unw_goodman_tff_axioms_hold_def
  using unw_pure_prop_definition unw_pure_op_definition
    unw_fun_prop_definition unw_fun_op_definition
    unw_top_truth unw_bottom_falsity unw_identity_application
    unw_negation_truth unw_box_truth unw_pure_top unw_pure_bottom
    unw_pure_identity unw_pure_negation unw_pure_box
    unw_pure_application_prop unw_unique_fundamental_proposition
    unw_no_fundamental_op1 unw_no_fundamental_op2
    unw_zeroary_recombination unw_zeroary_exhaustion
    unw_unary_recombination unw_unary_exhaustion
    unw_modalized_functionality_op1 unw_modalized_functionality_op2
    unw_goodman_PP
  by blast

corollary unw_goodman_inconsistency_target_is_false:
  "unw_goodman_tff_axioms_hold \<and> \<not> False"
  using unw_goodman_tff_model_certificate by simp

end
